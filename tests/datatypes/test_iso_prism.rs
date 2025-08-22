use rustica::datatypes::iso_prism::IsoPrism;
use rustica::traits::iso::Iso;

#[derive(Clone, Debug, PartialEq)]
enum MyEnum {
    Foo(i32),
    Bar(String),
}

// Prism Iso focusing on Foo(i32)
struct FooPrismIso;
impl Iso<MyEnum, Option<i32>> for FooPrismIso {
    type From = MyEnum;
    type To = Option<i32>;

    fn forward(&self, from: &MyEnum) -> Option<i32> {
        match from {
            MyEnum::Foo(x) => Some(*x),
            _ => None,
        }
    }

    fn backward(&self, to: &Option<i32>) -> MyEnum {
        match to {
            Some(x) => MyEnum::Foo(*x),
            None => MyEnum::Bar("default".to_string()),
        }
    }
}

// Secondary prism Iso: i32 <-> Option<String> for composition
struct ToStringPrismIso;
impl Iso<i32, Option<String>> for ToStringPrismIso {
    type From = i32;
    type To = Option<String>;

    fn forward(&self, from: &i32) -> Option<String> {
        Some(from.to_string())
    }

    fn backward(&self, to: &Option<String>) -> i32 {
        to.as_ref().and_then(|s| s.parse::<i32>().ok()).unwrap_or(0)
    }
}

#[test]
fn test_iso_prism_new_preview_review() {
    let prism = IsoPrism::new(FooPrismIso);

    let foo = MyEnum::Foo(10);
    let bar = MyEnum::Bar("hi".to_string());

    // preview
    assert_eq!(prism.preview(&foo), Some(10));
    assert_eq!(prism.preview(&bar), None);

    // review
    let reviewed = prism.review(&20);
    assert_eq!(reviewed, MyEnum::Foo(20));
}

#[test]
fn test_iso_prism_laws() {
    let prism = IsoPrism::new(FooPrismIso);

    // Review-Preview: preview(review(a)) == Some(a)
    let a = 123;
    assert_eq!(prism.preview(&prism.review(&a)), Some(a));

    // Preview-Review: if preview(s) = Some(a) then review(a) == s
    let s = MyEnum::Foo(77);
    if let Some(a2) = prism.preview(&s) {
        assert_eq!(prism.review(&a2), s);
    } else {
        panic!("Expected Some from preview");
    }
}

#[test]
fn test_iso_prism_composition_preview_review() {
    let foo_prism = IsoPrism::new(FooPrismIso);
    let to_string_prism = IsoPrism::new(ToStringPrismIso);
    let composed = foo_prism.compose(to_string_prism);

    // preview through composition
    let s1 = MyEnum::Foo(10);
    let s2 = MyEnum::Bar("x".to_string());
    assert_eq!(composed.preview(&s1), Some("10".to_string()));
    assert_eq!(composed.preview(&s2), None);

    // review through composition
    let s_new = composed.review(&"42".to_string());
    assert_eq!(s_new, MyEnum::Foo(42));
}

#[test]
fn test_iso_prism_composed_laws() {
    let composed = IsoPrism::new(FooPrismIso).compose(IsoPrism::new(ToStringPrismIso));

    // Review-Preview law on composed prism
    let b = "37".to_string();
    assert_eq!(composed.preview(&composed.review(&b)), Some(b.clone()));

    // Preview-Review law on composed prism
    let s = MyEnum::Foo(314);
    if let Some(b2) = composed.preview(&s) {
        assert_eq!(composed.review(&b2), s);
    } else {
        panic!("Expected Some from composed.preview");
    }
}
