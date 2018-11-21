#![feature(box_patterns)]
#![feature(box_syntax)]

#![allow(dead_code)]
#![allow(unused_variables)]

use std::fmt;

#[derive(Debug, Clone)]
struct I(char);

#[derive(Debug, Clone)]
struct M(char);

#[derive(Debug, Clone)]
struct Tensor<A, B>(A, B);

#[derive(Debug, Clone)]
enum Sigma<V> {
    Abs(Option<V>),
    App(V, V),
}

impl<V: fmt::Display> fmt::Display for Sigma<V> {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ::Sigma::*;
        match self {
            Abs(Some(term)) => write!(f, "λx.{}", term),
            Abs(None) => write!(f, "{}", "λx.x"),
            App(v1, v2) => write!(f, "{} {}", v1, v2),
        }
    }
}

fn sigma_map<A, B>(f: impl Fn(A) -> B, s: Sigma<A>) -> Sigma<B> {
    use ::Sigma::*;
    match s {
        Abs(o) => Abs(o.map(f)),
        App(v1, v2) => App(f(v1), f(v2)),
    }
}

#[derive(Debug, Clone)]
enum Mu {
    Var(I),
    Struct(Box<Sigma<Mu>>),
    Metavar(Tensor<M, Box<Mu>>),
}

impl fmt::Display for Mu {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ::Mu::*;
        match self {
            Var(i) => write!(f, "{}", i.0),
            Struct(s) => write!(f, "({})", s),
            Metavar(Tensor(m, box mu)) => write!(f, "{} ⊗ {}", m.0, mu),
        }
    }
}

fn s<X, Y: Clone>(t: Tensor<Sigma<X>, Y>) -> Sigma<Tensor<X, Y>> {
    let Tensor(sx, y) = t;
    sigma_map(|v| Tensor(v, y.clone()), sx)
}

fn sigma<A, P: Clone>(t: Tensor<Mu, P>, epsilon: &impl Fn(P) -> A, phi: &impl Fn(Sigma<A>) -> A, kappa: &impl Fn(Tensor<M, A>) -> A) -> A {
    use ::Mu::*;
    let Tensor(m, p) = t;
    match m {
        Var(_) => epsilon(p),
        Struct(sm) => phi(sigma_map(|x| sigma(x, epsilon, phi, kappa), s(Tensor(*sm, p)))),
        Metavar(Tensor(mv, x)) => kappa(Tensor(mv, sigma(Tensor(*x, p), epsilon, phi, kappa))),
    }
}

fn mult(m1: Mu, m2: Mu) -> Mu {
    use ::Mu::*;
    sigma(Tensor(m1, m2), &|m| m, &|s| Struct(box s), &|t| {
        let Tensor(a, b) = t;
        Metavar(Tensor(a, box b))
    })
}

fn main() {
    use ::Mu::*;
    use ::Sigma::*;
    let (a, b, c, d, e) = (Var(I('a')), Var(I('b')), Var(I('c')), Var(I('d')), Var(I('e')));
    let s = Struct(box Abs(Some(Struct(box App(b, c)))));
    let t = Struct(box App(d, e));
    println!("{} ⊗ {} -> {z}\n{z:?}", s.clone(), t.clone(), z = mult(s, t));
}