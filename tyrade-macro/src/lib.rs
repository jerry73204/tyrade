use proc_macro::TokenStream;

mod macro_utils;
mod trans;

#[proc_macro]
pub fn tyrade(tokens: TokenStream) -> TokenStream {
    macro_utils::tyrade(tokens)
}
