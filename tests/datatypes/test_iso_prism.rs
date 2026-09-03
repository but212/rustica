use rustica::datatypes::iso_prism::IsoPrism;
use rustica::traits::iso::Iso;

// --- Test Data Structures ---

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

#[derive(Clone, Debug, PartialEq)]
enum Shape {
    Circle { radius: f64 },
    Rectangle { width: f64, height: f64 },
}

#[derive(Clone, Debug, PartialEq)]
enum Drawing {
    Shape(Shape),
    Text(String),
}

struct ShapeIso;
impl Iso<Drawing, Option<Shape>> for ShapeIso {
    type From = Drawing;
    type To = Option<Shape>;

    fn forward(&self, from: &Drawing) -> Option<Shape> {
        match from {
            Drawing::Shape(shape) => Some(shape.clone()),
            Drawing::Text(_) => None,
        }
    }

    fn backward(&self, to: &Option<Shape>) -> Drawing {
        match to {
            Some(shape) => Drawing::Shape(shape.clone()),
            None => Drawing::Text("Placeholder".to_string()),
        }
    }
}

struct CircleIso;
impl Iso<Shape, Option<f64>> for CircleIso {
    type From = Shape;
    type To = Option<f64>;

    fn forward(&self, from: &Shape) -> Option<f64> {
        match from {
            Shape::Circle { radius } => Some(*radius),
            Shape::Rectangle { .. } => None,
        }
    }

    fn backward(&self, to: &Option<f64>) -> Shape {
        match to {
            Some(radius) => Shape::Circle { radius: *radius },
            None => Shape::Rectangle {
                width: 0.0,
                height: 0.0,
            },
        }
    }
}

// --- Test Cases ---

#[test]
fn test_iso_prism_core_laws_and_behavior() {
    let prism = IsoPrism::new(FooPrismIso);
    let foo = MyEnum::Foo(10);
    let bar = MyEnum::Bar("hi".to_string());

    // 1. Basic Operations
    assert_eq!(prism.preview(&foo), Some(10));
    assert_eq!(prism.preview(&bar), None);
    assert_eq!(prism.review(&20), MyEnum::Foo(20));

    // 2. Prism Laws
    // Law 1: Review-Preview: preview(review(a)) == Some(a)
    let a = 123;
    assert_eq!(prism.preview(&prism.review(&a)), Some(a));

    // Law 2: Preview-Review: if preview(s) = Some(a) then review(a) == s
    if let Some(a2) = prism.preview(&foo) {
        assert_eq!(prism.review(&a2), foo);
    }
}

#[test]
fn test_iso_prism_composition_and_laws() {
    let composed = IsoPrism::new(FooPrismIso).compose(IsoPrism::new(ToStringPrismIso));
    let s1 = MyEnum::Foo(10);

    // 1. Preview and Review through composition
    assert_eq!(composed.preview(&s1), Some("10".to_string()));
    assert_eq!(composed.preview(&MyEnum::Bar("x".to_string())), None);
    assert_eq!(composed.review(&"42".to_string()), MyEnum::Foo(42));

    // 2. Verify laws on composed prism
    // Review-Preview
    let b = "37".to_string();
    assert_eq!(composed.preview(&composed.review(&b)), Some(b));

    // Preview-Review
    if let Some(b2) = composed.preview(&s1) {
        assert_eq!(composed.review(&b2), s1);
    }
}

#[test]
fn test_iso_prism_nested_composition() {
    let composed = IsoPrism::new(ShapeIso).compose(IsoPrism::new(CircleIso));
    let circle_drawing = Drawing::Shape(Shape::Circle { radius: 5.0 });
    let rect_drawing = Drawing::Shape(Shape::Rectangle {
        width: 3.0,
        height: 4.0,
    });
    let text_drawing = Drawing::Text("Hello".to_string());

    assert_eq!(composed.preview(&circle_drawing), Some(5.0));
    assert_eq!(composed.preview(&rect_drawing), None);
    assert_eq!(composed.preview(&text_drawing), None);
    assert_eq!(
        composed.review(&10.0),
        Drawing::Shape(Shape::Circle { radius: 10.0 })
    );
}
