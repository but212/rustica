use rustica::datatypes::io::IO;

#[test]
fn test_io_monadic_fundamentals() {
    let pure_io = IO::pure(42);
    let effect_io = IO::new(|| 42);
    assert!(pure_io.is_pure() && effect_io.is_effect());

    let f = |x: i32| IO::pure(x * 2);
    assert_eq!(IO::pure(10).bind(f).run(), 20);
    assert_eq!(pure_io.clone().bind(IO::pure).run(), 42);

    let val = IO::pure(5);
    let app_f = IO::new(|| {
        let multiplier = 3;
        move |x: i32| x * multiplier
    });
    assert_eq!(val.apply(app_f).run(), 15);

    let complex = pure_io.fmap(|x| x + 8).bind(|x| IO::new(move || x / 2));
    assert_eq!(complex.run(), 25);
}
