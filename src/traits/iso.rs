pub trait Iso<A, B> {
    fn to(&self, a: &A) -> B;
    fn from(&self, b: &B) -> A;
}
