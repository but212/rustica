use rustica::datatypes::cont;

#[test]
fn test_cont_chaining_and_laws() {
    let c = cont::Cont::return_cont(10);
    let chain = c
        .clone()
        .fmap(|x| x * 2)
        .bind(|x| cont::Cont::return_cont(x + 5))
        .fmap(|x| x - 3);
    assert_eq!(chain.run(|x| x), 22);

    assert_eq!(
        c.clone().bind(cont::Cont::return_cont).run(|x| x),
        c.run(|x| x)
    );
}
