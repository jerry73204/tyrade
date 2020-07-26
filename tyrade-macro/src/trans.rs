use itertools::Itertools;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use std::{
    collections::{HashMap, HashSet},
    iter::Sum,
    ops::Add,
};
use syn::{
    parse2, visit_mut::VisitMut, BinOp, Block, Expr, ExprBinary, ExprBlock, ExprCall, ExprIf,
    ExprMatch, ExprPath, ExprTuple, Fields, FnArg, GenericParam, Ident, Item, ItemEnum, ItemFn,
    Pat, PatIdent, Path, PathSegment, ReturnType, Stmt, Type, TypeParam, TypePath,
};

// HACK: have to do this without HKT :(
const BASE_KINDS: &[&str] = &["TNum", "TBool", "TList"];

fn type_to_ident(ty: &Type) -> Option<Ident> {
    if let Type::Path(TypePath { path, .. }) = ty {
        Some(path.get_ident().unwrap().clone())
    } else {
        None
    }
}

fn ident_to_type(ident: &Ident) -> Type {
    let segment = PathSegment::from(ident.clone());
    let path = Path::from(segment);
    Type::Path(TypePath { path, qself: None })
}

fn str_to_type<T: Into<String>>(t: T) -> Type {
    let ident = Ident::new(&t.into(), Span::call_site());
    ident_to_type(&ident)
}

fn block_to_expr(block: Block) -> Expr {
    Expr::Block(ExprBlock {
        attrs: vec![],
        label: None,
        block,
    })
}

fn kind_to_type(kind: &Ident) -> Option<Type> {
    if &format!("{}", kind) == "Type" {
        None
    } else {
        Some(ident_to_type(kind))
    }
}

pub fn translate_enum(enum_: ItemEnum) -> TokenStream {
    let trait_name = &enum_.ident;

    let types = enum_.variants.iter().map(|variant| {
    let name = &variant.ident;
    let params = match &variant.fields {
      Fields::Unnamed(unnamed) => {
        unnamed.unnamed.iter().enumerate().map(|(i, field)| {
          let kind = type_to_ident(&field.ty)
            .unwrap_or_else(|| unimplemented!());
          (str_to_type(format!("T{}", i)), kind)
        }).collect::<Vec<_>>()
      },
      Fields::Unit => vec![],
      _ => unimplemented!()
    };

    let params_with_bounds = params.iter().map(|(id, kind)| {
      match kind_to_type(kind) {
        Some(_) => quote!{ #id: #kind },
        None => quote!{ #id }
      }
    }).collect::<Vec<_>>();

    let just_params = params.iter().map(|(id, _)| quote!{ #id } )
      .collect::<Vec<_>>();


    let compute_trait = if just_params.len() > 0 {
      let compute_name = Ident::new(
        &format!("Compute{}", name), Span::call_site());
      let first_param = &just_params[0];
      let remaining_params = &just_params[1..];
      quote! {
        pub trait #compute_name<#(#remaining_params),*> {}
        impl<#(#params_with_bounds),*> #compute_name<#(#remaining_params),*> for #first_param {}
      }
    } else {
      quote! {}
    };

    quote!{
      pub struct #name<#(#params_with_bounds),*>(
        pub ::std::marker::PhantomData<(#(#just_params),*)>
      );
      impl<#(#params_with_bounds),*> #trait_name for #name<#(#just_params),*> {}
      #compute_trait
    }
  }).collect::<Vec<_>>();

    quote! {
      pub trait #trait_name {}
      #(#types)*
    }
}

#[derive(Clone, Debug)]
struct FnTransEnv {
    args: Vec<Type>,
    quantifiers: Vec<Ident>,
    bounds: HashMap<Type, Vec<Type>>,
    substitutions: HashMap<Ident, Type>,
}

impl Add<Self> for FnTransEnv {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let args = self
            .args
            .iter()
            .zip(other.args.iter())
            .map(|(arg1, arg2)| {
                // Pick the "biggest" arg (e.g. prefer F<X> over Y)
                // If both are specialized, should be an error
                if let Type::Path(_) = arg1 {
                    arg2
                } else {
                    arg1
                }
            })
            .cloned()
            .collect::<Vec<_>>();

        let quantifiers: Vec<_> = itertools::merge(self.quantifiers, other.quantifiers)
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();
        let bounds: HashMap<_, Vec<_>> = self
            .bounds
            .into_iter()
            .chain(other.bounds)
            .into_group_map()
            .into_iter()
            .map(|(k, vecs)| {
                let v: Vec<_> = vecs.into_iter().flatten().collect();
                (k, v)
            })
            .collect();

        // TODO: is this correct?
        let substitutions: HashMap<_, _> = self
            .substitutions
            .into_iter()
            .chain(other.substitutions)
            .collect();

        FnTransEnv {
            args,
            quantifiers,
            bounds,
            substitutions,
        }
    }
}

impl Sum<Self> for FnTransEnv {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.fold1(|lhs, rhs| lhs + rhs).unwrap()
    }
}

#[derive(Debug, Clone)]
struct FnTransOutput {
    output_ty: TokenStream,
    env: FnTransEnv,
}

impl FnTransOutput {
    fn merge<F>(outputs: Vec<Vec<FnTransOutput>>, f: F) -> Vec<FnTransOutput>
    where
        F: Fn(FnTransEnv, Vec<TokenStream>) -> FnTransOutput,
    {
        outputs
            .into_iter()
            .map(|v| v.into_iter())
            .multi_cartesian_product()
            .map(|outp| {
                let args: Vec<_> = outp.clone().into_iter().map(|o| o.output_ty).collect();
                let merged_env: FnTransEnv = outp.into_iter().map(|out| out.env).sum();
                f(merged_env, args)
            })
            .collect::<Vec<_>>()
    }
}

fn translate_expr(env: &FnTransEnv, cur_kind: &Ident, expr: &Expr) -> Vec<FnTransOutput> {
    match expr {
        Expr::Match(match_) => translate_match_expr(env, cur_kind, match_),
        Expr::Path(path) => translate_path_expr(env, cur_kind, path),
        Expr::Tuple(tuple) => translate_tuple_expr(env, cur_kind, tuple),
        Expr::Binary(binop) => translate_binary_expr(env, cur_kind, binop),
        Expr::If(if_) => translate_if_expr(env, cur_kind, if_),
        Expr::Block(block) => translate_block_expr(env, cur_kind, block),
        Expr::Call(call) => translate_call_expr(env, cur_kind, call),
        Expr::Paren(paren) => translate_expr(env, cur_kind, &paren.expr),
        _ => unimplemented!("expr: {:?}", expr),
    }
}

fn translate_match_expr(
    env: &FnTransEnv,
    cur_kind: &Ident,
    match_: &ExprMatch,
) -> Vec<FnTransOutput> {
    let matched_ident = if let Expr::Path(path) = &*match_.expr {
        path.path.get_ident().unwrap()
    } else {
        unimplemented!("match expr")
    };

    let match_ty = ident_to_type(matched_ident);
    let arg_idx = env
        .args
        .iter()
        .position(|arg| arg == &match_ty)
        .expect(&format!("Invalid match on {}", matched_ident));

    match_
        .arms
        .iter()
        .map(|arm| {
            let (variant, fields) = translate_pat(&arm.pat);

            let mut env = env.clone();
            let field_names = fields
                .iter()
                .map(|(ident, _)| ident)
                .cloned()
                .collect::<Vec<_>>();

            // if args = [X, Y] and expr is match Y { Q(Z) => ... }
            // then update args to be [X, Q<Z>]
            let new_type: Type = parse2(quote! {
              #variant<#(#field_names),*>
            })
            .unwrap();
            env.args[arg_idx] = new_type.clone();

            // if quantifiers = [X, Y] then replace [Y] with [Z]
            env.quantifiers = env
                .quantifiers
                .into_iter()
                .filter(|ident| ident != matched_ident)
                .collect::<Vec<_>>();
            env.quantifiers.extend(field_names);

            // if bounds = {Y: Foo<X>} then rename to {Q<Z>: Foo<X>}
            let bounds = env.bounds.remove(&ident_to_type(&matched_ident)).unwrap();
            env.bounds.insert(new_type.clone(), bounds);

            // add field bounds
            for (ident, kind) in fields.iter() {
                if let Some(kind) = kind_to_type(kind) {
                    env.bounds.insert(ident_to_type(ident), vec![kind]);
                }
            }

            // add substitution for Y -> Q<Z>
            env.substitutions.insert(matched_ident.clone(), new_type);

            translate_expr(&env, cur_kind, &arm.body)
        })
        .flatten()
        .collect::<Vec<_>>()
}

fn translate_path_expr(env: &FnTransEnv, _cur_kind: &Ident, path: &ExprPath) -> Vec<FnTransOutput> {
    let ident = path.path.get_ident().unwrap();
    let ty = env
        .substitutions
        .get(&ident)
        .cloned()
        .unwrap_or_else(|| ident_to_type(ident));
    vec![FnTransOutput {
        env: env.clone(),
        output_ty: quote! { #ty },
    }]
}

fn translate_tuple_expr(
    env: &FnTransEnv,
    _cur_kind: &Ident,
    tuple: &ExprTuple,
) -> Vec<FnTransOutput> {
    if tuple.elems.len() == 0 {
        vec![FnTransOutput {
            env: env.clone(),
            output_ty: quote! { () },
        }]
    } else {
        unimplemented!("tuple")
    }
}

fn translate_binary_expr(
    env: &FnTransEnv,
    cur_kind: &Ident,
    binop: &ExprBinary,
) -> Vec<FnTransOutput> {
    let ExprBinary {
        left, right, op, ..
    } = binop;
    let op = match op {
        BinOp::Eq(_) => quote! { TypeEquals },
        BinOp::And(_) => quote! { TAnd },
        BinOp::Le(_) => quote! { TLessThanEqual },
        BinOp::Add(_) => quote! { TAdd },
        BinOp::Div(_) => quote! { TDivide },
        BinOp::Sub(_) => quote! { TSub },
        _ => unimplemented!("binop {:?}", binop.op),
    };
    let trans_expr: Expr = parse2(quote! { #op(#left, #right) }).unwrap();
    translate_expr(env, cur_kind, &trans_expr)
}

fn translate_if_expr(env: &FnTransEnv, cur_kind: &Ident, if_: &ExprIf) -> Vec<FnTransOutput> {
    let ExprIf {
        cond,
        then_branch,
        else_branch,
        ..
    } = if_;
    let (_else_token, else_) = else_branch
        .as_ref()
        .expect("If expression must have an 'else'");

    let if_name = Ident::new(&format!("TIf{}", cur_kind), Span::call_site());
    let trans_expr: Expr = parse2(quote! { #if_name(#cond, #then_branch, #else_) }).unwrap();
    translate_expr(env, cur_kind, &trans_expr)
}

fn translate_block_expr(
    env: &FnTransEnv,
    cur_kind: &Ident,
    block: &ExprBlock,
) -> Vec<FnTransOutput> {
    if let Stmt::Expr(expr) = &block.block.stmts[0] {
        translate_expr(env, cur_kind, &expr)
    } else {
        unimplemented!("block")
    }
}

fn translate_call_expr(env: &FnTransEnv, cur_kind: &Ident, call: &ExprCall) -> Vec<FnTransOutput> {
    let ExprCall { func, args, .. } = call;

    let func_ident = if let Expr::Path(path) = &**func {
        path.path.get_ident().unwrap()
    } else {
        unimplemented!("func ident")
    };

    let args_vec: Vec<_> = args
        .iter()
        .map(|arg| translate_expr(env, cur_kind, arg))
        .collect();

    FnTransOutput::merge(args_vec, |mut env, args| {
        let first_arg: Type = parse2(args[0].clone()).unwrap();
        let bounds = env
            .bounds
            .entry(first_arg.clone())
            .or_insert_with(|| Vec::new());
        let compute_ident = Ident::new(&format!("Compute{}", func_ident), Span::call_site());
        let remaining_args = &args[1..];
        bounds.push(parse2(quote! { #compute_ident<#(#remaining_args),*> }).unwrap());

        let output_ty = quote! { #func_ident<#(#args),*> };
        FnTransOutput { output_ty, env }
    })
}

fn translate_pat(pat: &Pat) -> (Ident, Vec<(Ident, Ident)>) {
    match pat {
        Pat::Ident(PatIdent { ident, .. }) => (ident.clone(), vec![]),
        Pat::TupleStruct(tuple_struct) => {
            let variant = tuple_struct.path.get_ident().unwrap().clone();
            let fields = tuple_struct
                .pat
                .elems
                .iter()
                .map(|p| {
                    if let Pat::Ident(PatIdent { ident, subpat, .. }) = &p {
                        let kind = if let Some((_, p2)) = subpat {
                            if let Pat::Ident(PatIdent { ident, .. }) = &**p2 {
                                ident.clone()
                            } else {
                                panic!("RHS of @ must be an ident")
                            }
                        } else {
                            panic!("Match tuple struct must have @ trait annotation")
                        };

                        (ident.clone(), kind)
                    } else {
                        unimplemented!("match pat ident")
                    }
                })
                .collect::<Vec<_>>();
            (variant, fields)
        }
        _ => unimplemented!("match pat"),
    }
}

fn gen_impls(fn_: ItemFn) -> TokenStream {
    let fn_name = &fn_.sig.ident;
    let compute_name = Ident::new(&format!("Compute{}", fn_.sig.ident), Span::call_site());

    let args = fn_
        .sig
        .inputs
        .iter()
        .map(|arg| {
            if let FnArg::Typed(pat_type) = arg {
                if let Pat::Ident(PatIdent { ident, .. }) = &*pat_type.pat {
                    (ident, type_to_ident(&pat_type.ty).unwrap())
                } else {
                    unimplemented!("fn arg pat")
                }
            } else {
                unreachable!("fn arg")
            }
        })
        .collect::<Vec<_>>();

    // Construct initial translation environment from args
    let init_args = args
        .iter()
        .map(|(arg, _)| ident_to_type(arg))
        .collect::<Vec<_>>();
    let init_quantifiers = args
        .iter()
        .map(|(arg, _)| (**arg).clone())
        .collect::<Vec<_>>();
    let init_bounds = args
        .iter()
        .filter_map(|(arg, kind)| kind_to_type(kind).map(|kind| (ident_to_type(arg), vec![kind])))
        .collect::<HashMap<_, _>>();
    let init_env = FnTransEnv {
        args: init_args,
        quantifiers: init_quantifiers,
        bounds: init_bounds,
        substitutions: HashMap::new(),
    };

    let return_kind: Type = if let ReturnType::Type(_, kind) = &fn_.sig.output {
        (**kind).clone()
    } else {
        panic!("Function must have return type")
    };

    // Run translation
    let fn_trans_outputs = translate_expr(
        &init_env,
        &type_to_ident(&return_kind).unwrap(),
        &block_to_expr(*fn_.block.clone()),
    );

    // Convert each path into an impl block
    let impls = fn_trans_outputs
        .iter()
        .map(|outp| {
            let output_ty = &outp.output_ty;
            let args = &outp.env.args;
            let first_arg = &args[0];
            let remaining_args = &args[1..];

            let quantifiers = &outp.env.quantifiers;
            let bounds = outp
                .env
                .bounds
                .iter()
                .map(|(ty, bounds)| quote! { #ty : #(#bounds)+* })
                .collect::<Vec<_>>();

            quote! {
              impl<#(#quantifiers),*> #compute_name<#(#remaining_args),*>
                for #first_arg
              where #(#bounds),*
              {
                type Output = #output_ty;
              }
            }
        })
        .collect::<Vec<_>>();

    // Get names needed for trait declaration
    let (arg_names, _): (Vec<_>, Vec<_>) = args.iter().cloned().skip(1).unzip();
    let (first_name, first_ty) = args[0].clone();
    let return_kind = kind_to_type(&type_to_ident(&return_kind).unwrap())
        .map(|kind| quote! { #kind })
        .unwrap_or_else(|| quote! {});
    quote! {
      pub trait #compute_name<#(#arg_names),*>: #first_ty {
        type Output: #return_kind;
      }

      pub type #fn_name<#first_name,#(#arg_names),*> =
        <#first_name as #compute_name<#(#arg_names),*>>::Output;

      #(#impls)*
    }
}

struct Rename {
    src: Ident,
    dst: Ident,
}

impl VisitMut for Rename {
    fn visit_ident_mut(&mut self, node: &mut Ident) {
        if &self.src == node {
            *node = self.dst.clone();
        }
    }
}

fn rename(fn_: &mut ItemFn, src: Ident, dst: Ident) {
    let mut renamer = Rename { src, dst };
    renamer.visit_item_fn_mut(fn_);
}

pub fn translate_fn(fn_: ItemFn) -> TokenStream {
    let generics = &fn_.sig.generics.params;
    let impls = if generics.len() > 0 {
        if let GenericParam::Type(TypeParam { ident, .. }) = &generics[0] {
            BASE_KINDS
                .iter()
                .map(|base_kind| {
                    let mut fn_ = fn_.clone();

                    // Instantiate generic kind K as base_kind
                    rename(
                        &mut fn_,
                        ident.clone(),
                        Ident::new(base_kind, Span::call_site()),
                    );

                    let fn_name = fn_.sig.ident.clone();
                    let new_name = format!("{}{}", fn_name, base_kind);
                    rename(
                        &mut fn_,
                        fn_name.clone(),
                        Ident::new(&new_name, Span::call_site()),
                    );

                    gen_impls(fn_)
                })
                .collect::<Vec<TokenStream>>()
        } else {
            unimplemented!("generics")
        }
    } else {
        vec![gen_impls(fn_)]
    };

    quote! { #(#impls)* }
}

pub fn translate_item(item: Item) -> TokenStream {
    match item {
        Item::Enum(enum_) => translate_enum(enum_),
        Item::Fn(fn_) => translate_fn(fn_),
        _ => unimplemented!("item"),
    }
}
