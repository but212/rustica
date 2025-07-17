#[test]
fn core_type_classes_functor() {
    use rustica::datatypes::maybe::Maybe;
    use rustica::traits::functor::Functor;

    let just_five = Maybe::Just(5);
    let doubled = just_five.fmap(|x| x * 2); // Maybe::Just(10)
    assert_eq!(doubled, Maybe::Just(10));
}

#[test]
fn core_type_classes_applicative() {
    use rustica::datatypes::validated::Validated;
    use rustica::traits::applicative::Applicative;

    let valid1: Validated<&str, i32> = Validated::valid(5);
    let valid2: Validated<&str, i32> = Validated::valid(10);
    let combined = valid1.lift2(&valid2, |a, b| a + b); // Validated::Valid(15)
    assert_eq!(combined, Validated::Valid(15));
}

#[test]
fn core_type_classes_monad() {
    use rustica::datatypes::either::Either;
    use rustica::traits::monad::Monad;

    let right: Either<&str, i32> = Either::right(5);
    let result = right
        .bind(|x| Either::right(x + 1))
        .bind(|x| Either::right(x * 2)); // Either::Right(12)
    assert_eq!(result, Either::Right(12));
}

#[test]
fn core_data_types_maybe() {
    use rustica::datatypes::maybe::Maybe;

    let just_value = Maybe::Just(42);
    let nothing_value: Maybe<i32> = Maybe::Nothing;
    assert_eq!(just_value, Maybe::Just(42));
    assert_eq!(nothing_value, Maybe::Nothing);
}

#[test]
fn core_data_types_either() {
    use rustica::datatypes::either::Either;

    let left: Either<i32, &str> = Either::Left(42);
    let right: Either<i32, &str> = Either::Right("hello");
    assert_eq!(left, Either::Left(42));
    assert_eq!(right, Either::Right("hello"));
}

#[test]
fn core_data_types_validated() {
    use rustica::datatypes::validated::Validated;

    let valid: Validated<&str, i32> = Validated::valid(42);
    let invalid: Validated<&str, i32> = Validated::invalid("validation error");
    assert_eq!(valid, Validated::valid(42));
    assert_eq!(invalid, Validated::invalid("validation error"));
}

#[test]
fn core_data_types_persistent_vector() {
    use rustica::pvec::pvec;

    // Create using macro
    let vec1 = pvec![1, 2, 3];

    // Create new vector with additional element (original unchanged)
    let vec3 = vec1.push_back(4);

    // Update an element (returns new vector, original unchanged)
    let vec4 = vec3.update(1, 20);

    // Small vectors (≤8 elements) use optimized storage
    assert_eq!(vec1.get(0), Some(&1));
    assert_eq!(vec3.get(1), Some(&2));
    assert_eq!(vec4.get(1), Some(&20));
}

#[test]
fn core_data_types_choice() {
    use rustica::datatypes::choice::Choice;
    use rustica::traits::functor::Functor;

    // Create a choice with a primary value and alternatives
    let choice = Choice::new(1, vec![2, 3, 4]);

    // Access the primary value
    assert_eq!(choice.first(), Some(&1));

    // Transform all values using the Functor trait
    let doubled = choice.fmap(|x| x * 2);
    assert_eq!(doubled.first(), Some(&2));

    // Filter alternatives based on a predicate
    let even_only = choice.filter(|x| x % 2 == 0);

    // Swap the primary value with an alternative
    let swapped = choice.swap_with_alternative(1);
    assert_eq!(swapped.first(), Some(&3));
    assert!(swapped.alternatives().contains(&1));
    assert_eq!(even_only.alternatives(), vec![2, 4]);
}
