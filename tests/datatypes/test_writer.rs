#[cfg(feature = "serde")]
use rustica::datatypes::writer::Writer;
#[cfg(feature = "serde")]
use rustica::traits::monoid::Monoid;
#[cfg(feature = "serde")]
use rustica::traits::semigroup::Semigroup;

#[cfg(feature = "serde")]
#[derive(Clone, Debug, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
struct Log(Vec<String>);

#[cfg(feature = "serde")]
impl Semigroup for Log {
    fn combine(&self, other: &Self) -> Self {
        let mut combined = self.0.clone();
        combined.extend(other.0.clone());
        Log(combined)
    }

    fn combine_owned(self, other: Self) -> Self {
        let mut combined = self.0;
        combined.extend(other.0);
        Log(combined)
    }
}

#[cfg(feature = "serde")]
impl Monoid for Log {
    fn empty() -> Self {
        Log(Vec::new())
    }
}

#[cfg(feature = "serde")]
#[test]
fn test_writer_serde() {
    let writer = Writer::new(Log(vec!["log".into()]), 42);
    let json = serde_json::to_string(&writer).unwrap();
    let back: Writer<Log, i32> = serde_json::from_str(&json).unwrap();
    assert_eq!(writer, back);
}
