pub trait Identity {
    fn identity<T>(x: T) -> T {
        x
    }
}