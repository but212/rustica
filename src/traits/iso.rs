pub trait Iso<A, B> {
    type To;
    type From;
    fn forward(from: &Self::From) -> Self::To;
    fn backward(to: &Self::To) -> Self::From;
}
