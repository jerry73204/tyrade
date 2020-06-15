use tyrade::*;
use std::marker::PhantomData;

tyrade! {
  enum SessionType {
    Close,
    Recv(Type, SessionType),
    Send(Type, SessionType),
    Choose(SessionType, SessionType),
    Offer(SessionType, SessionType),
    Label(SessionType),
    Goto(TNum)
  }

  fn Dual(S: SessionType) -> SessionType {
    match S {
      Close => S,
      Recv(T @ Type, S2 @ SessionType) => Send(T, Dual(S2)),
      Send(T @ Type, S2 @ SessionType) => Recv(T, Dual(S2)),
      Choose(S2 @ SessionType, S3 @ SessionType) => Offer(Dual(S2), Dual(S3)),
      Offer(S2 @ SessionType, S3 @ SessionType) => Choose(Dual(S2), Dual(S3)),
      Label(S2 @ SessionType) => Label(Dual(S2)),
      Goto(N @ TNum) => S
    }
  }
}

struct Chan<Env, S>(PhantomData<(Env, S)>);

impl<Env: TList, S: SessionType> Chan<Env, Label<S>> {
  fn label(self) -> Chan<Cons<S, Env>, S> {
    Chan(PhantomData)
  }
}

impl<Env: TList, N: TNum> Chan<Env, Goto<N>>
where Env: ComputeTListNth<N> + ComputeTListSkip<N>
{
  fn goto(self) -> Chan<TListSkip<Env, N>, TListNth<Env, N>> {
    Chan(PhantomData)
  }
}

#[test]
fn session_type_test() {
  assert_type_eq::<Recv<i32, Close>, Dual<Send<i32, Close>>>();

  let c: Chan<
      Cons<Close, Nil>,
      Label<Goto<S<Z>>>> = Chan(PhantomData);
  let c: Chan<
      Cons<Goto<S<Z>>, Cons<Close, Nil>>,
      Goto<S<Z>>> = c.label();
  let _: Chan<Cons<Close, Nil>, Close> = c.goto();
}
