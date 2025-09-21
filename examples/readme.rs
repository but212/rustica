fn pvec_example() {
    use rustica::pvec::PersistentVector;
    use rustica::pvec::pvec;

    let v1: PersistentVector<i32> = pvec![1, 2, 3, 4, 5];
    let v2 = v1.push_back(6);
    let v3 = v1.update(0, 10);

    assert_eq!(v1.get(0), Some(&1));
    assert_eq!(v2.get(5), Some(&6));
    assert_eq!(v3.get(0), Some(&10));
}

fn id_monad() {
    use rustica::datatypes::id::Id;
    use rustica::prelude::*;
    use rustica::traits::identity::Identity;

    // Create Id values
    let x = Id::new(5);
    let y = Id::new(3);
    let z = Id::new(2);

    // Access the inner value using Identity trait's value() method
    assert_eq!(*x.value(), 5);

    // Using Functor to map over Id
    let doubled = x.fmap(|n| n * 2);
    assert_eq!(*doubled.value(), 10);

    // Using Pure to lift a value into Id context
    let pure_value = Id::<i32>::pure(&42);
    assert_eq!(*pure_value.value(), 42);

    // Using Applicative to apply functions
    // 1. Apply a function wrapped in Id
    let add_one = Id::new(|x: &i32| x + 1);
    let result = add_one.apply(&x);
    assert_eq!(*result.value(), 6);

    // 2. Combine two Id values with lift2
    let add = |a: &i32, b: &i32| a + b;
    let sum = Id::<i32>::lift2(add, &x, &y);
    assert_eq!(*sum.value(), 8);

    // 3. Combine three Id values with lift3
    let multiply = |a: &i32, b: &i32, c: &i32| a * b * c;
    let product = Id::<i32>::lift3(multiply, &x, &y, &z);
    assert_eq!(*product.value(), 30);

    // Working with different types
    let greeting = Id::new("Hello");
    let count = Id::new(3_usize);
    let repeat = |s: &&str, n: &usize| s.repeat(*n);
    let repeated = Id::<&str>::lift2(repeat, &greeting, &count);
    assert_eq!(*repeated.value(), "HelloHelloHello");

    // Chaining operations
    let result = x
        .fmap(|n| n + 1) // 5 -> 6
        .fmap(|n| n * 2) // 6 -> 12
        .fmap(|n| n.to_string());
    assert_eq!(*result.value(), "12");
}
fn cont_example() {
    use rustica::datatypes::cont::Cont;

    // Create a simple continuation
    let cont = Cont::return_cont(42);

    // Run the continuation with a handler
    let result = cont.clone().run(|x| x * 2);
    assert_eq!(result, 84);

    // Chain continuations
    let cont2 = cont.bind(|x| Cont::return_cont(x + 1));
    let result2 = cont2.run(|x| x * 2);
    assert_eq!(result2, 86);
}

use rustica::datatypes::cont::Cont;

// A function that uses continuations to implement early return
fn safe_divide(a: i32, b: i32) -> Cont<i32, i32> {
    if b == 0 {
        // Early return with a default value
        Cont::new(|_| -1)
    } else {
        // Continue with the division
        Cont::return_cont(a / b)
    }
}
fn control_flow_example() {
    let result1 = safe_divide(10, 2).run(|x| x);
    let result2 = safe_divide(10, 0).run(|x| x);

    assert_eq!(result1, 5);
    assert_eq!(result2, -1);
}

fn additional_examples_from_cont() {
    use rustica::datatypes::cont::Cont;

    // Create two continuations
    let cont1 = Cont::return_cont(5);
    let cont2 = Cont::return_cont(-1);

    // Run the continuations with an identity continuation
    let result1 = cont1.run(|x| x);
    let result2 = cont2.run(|x| x);

    assert_eq!(result1, 5);
    assert_eq!(result2, -1);
}

fn main() {
    pvec_example();
    id_monad();
    cont_example();
    control_flow_example();
    additional_examples_from_cont();
}
