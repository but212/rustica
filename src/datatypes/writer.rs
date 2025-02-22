use std::sync::Arc;
use std::any::Any;
use crate::traits::hkt::HKT;
use crate::traits::functor::Functor;
use crate::traits::pure::Pure;
use crate::traits::identity::Identity;
use crate::traits::semigroup::Semigroup;
use crate::traits::monoid::Monoid;
use crate::traits::hkt::{TypeOps, AnyBox};
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;

/// The Writer monad, representing computations with an accumulating log.
///
/// The Writer monad allows for computations that produce a value along with a log.
/// It's useful for adding logging to pure computations, accumulating errors, or
/// building up computations from sequences of steps.
///
/// # Examples
///
/// ```
/// use rustica::datatypes::writer::Writer;
/// use rustica::traits::monoid::Monoid;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::hkt::{TypeOps, AnyBox, HKT};
/// use std::sync::Arc;
/// use std::any::Any;
///
/// #[derive(Clone, Debug, PartialEq)]
/// struct Log(Vec<String>);
///
/// impl HKT for Log {
///     fn apply_type(&self) -> Arc<dyn Any + Send + Sync> {
///         Arc::new(self.clone())
///     }
///
///     fn downcast(&self, boxed: &Arc<dyn Any + Send + Sync>) -> Option<Arc<dyn Any + Send + Sync>> {
///         boxed.downcast_ref::<Log>()
///             .map(|l| Arc::new(l.clone()) as Arc<dyn Any + Send + Sync>)
///     }
/// }
///
/// impl Semigroup for Log {
///     fn combine(&self, other: AnyBox) -> AnyBox {
///         if let Some(other_log) = other.downcast_ref::<Log>() {
///             let mut combined = self.0.clone();
///             combined.extend(other_log.0.clone());
///             Arc::new(Log(combined))
///         } else {
///             Arc::new(self.clone())
///         }
///     }
/// }
///
/// impl Monoid for Log {
///     fn empty(&self) -> AnyBox {
///         Arc::new(Log(Vec::new()))
///     }
/// }
///
/// let writer = Writer::new(42, Log(vec!["Initial log".to_string()]));
/// let result = writer.run_writer();
/// let (value, log) = result.as_ref();
/// assert_eq!(value.downcast_ref::<i32>().unwrap(), &42);
/// assert_eq!(log, &Log(vec!["Initial log".to_string()]));
/// ```
#[derive(Clone)]
pub struct Writer<W: TypeOps + Semigroup + Monoid + Clone + 'static> {
    /// The function that produces a value and a log
    run: Arc<dyn Fn() -> Arc<(Arc<dyn Any + Send + Sync>, W)> + Send + Sync>,
}

impl<W: TypeOps + Semigroup + Monoid + Clone + 'static> Writer<W> {
    /// Creates a new Writer with a value and a log.
    ///
    /// # Arguments
    /// * `value` - The value to be wrapped in the Writer.
    /// * `log` - The initial log.
    ///
    /// # Returns
    /// A new `Writer` instance.
    pub fn new<A: Clone + Send + Sync + 'static>(value: A, log: W) -> Self {
        Writer {
            run: Arc::new(move || Arc::new((Arc::new(value.clone()), log.clone()))),
        }
    }

    /// Runs the writer computation and returns the value and the log.
    ///
    /// # Returns
    /// A type-erased tuple containing the value and the log.
    pub fn run_writer(&self) -> Arc<(Arc<dyn Any + Send + Sync>, W)> {
        (self.run)()
    }

    /// Gets the value from the writer computation.
    ///
    /// # Returns
    /// The type-erased value stored in the Writer.
    pub fn value(&self) -> Arc<dyn Any + Send + Sync> {
        let (value, _) = &*(self.run)();
        value.clone()
    }

    /// Gets the log from the writer computation.
    ///
    /// # Returns
    /// The log stored in the Writer.
    pub fn log(&self) -> W {
        let (_, log) = &*(self.run)();
        log.clone()
    }

    /// Executes a writer computation and returns only its log.
    ///
    /// # Returns
    /// The log from the computation.
    pub fn exec(&self) -> W {
        let (_, log) = &*(self.run)();
        log.clone()
    }
}

impl<W: TypeOps + Semigroup + Monoid + Clone + 'static> HKT for Writer<W> {
    fn apply_type(&self) -> Arc<dyn Any + Send + Sync> {
        Arc::new(self.clone())
    }

    fn downcast(&self, boxed: &Arc<dyn Any + Send + Sync>) -> Option<Arc<dyn Any + Send + Sync>> {
        boxed.downcast_ref::<Writer<W>>()
            .map(|w| Arc::new(w.clone()) as Arc<dyn Any + Send + Sync>)
    }
}

impl<W: TypeOps + Semigroup + Monoid + Clone + Default + 'static> Pure for Writer<W> {
    fn pure(value: AnyBox) -> AnyBox {
        let empty_w = W::default();
        Arc::new(Writer::new(value, empty_w)) as AnyBox
    }
}

impl<W: TypeOps + Semigroup + Monoid + Clone + Default + 'static> Identity for Writer<W> {
    fn identity() -> AnyBox {
        Arc::new(Writer::new(Arc::new(W::default()), W::default())) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Self::identity())
    }
}

impl<W: TypeOps + Semigroup + Monoid + Clone + Default + 'static> Functor for Writer<W> {
    fn fmap(&self, f: Arc<dyn Fn(Arc<dyn Any + Send + Sync>) -> Arc<dyn Any + Send + Sync> + Send + Sync>) -> Arc<dyn Any + Send + Sync> {
        let (value, log) = &*(self.run)();
        Arc::new(Writer::new(f(value.clone()), log.clone()))
    }
}

impl<W: TypeOps + Semigroup + Monoid + Clone + Default + 'static> Semigroup for Writer<W> {
    fn combine(&self, other: AnyBox) -> AnyBox {
        if let Some(other_writer) = other.downcast_ref::<Writer<W>>() {
            let (value1, log1) = &*(self.run)();
            let (_value2, log2) = &*(other_writer.run)();
            Arc::new(Writer::new(
                value1.clone(),
                log1.combine(Arc::new(log2.clone()) as AnyBox).downcast_ref::<W>().unwrap().clone()
            ))
        } else {
            Arc::new(self.clone())
        }
    }
}

impl<W: TypeOps + Semigroup + Monoid + Clone + Default + 'static> Monoid for Writer<W> {
    fn empty(&self) -> AnyBox {
        let (value, _) = &*(self.run)();
        let empty_log = self.log().empty().downcast_ref::<W>().unwrap().clone();
        Arc::new(Writer::new(value.clone(), empty_log))
    }
}

impl<W: TypeOps + Semigroup + Monoid + Clone + Default + 'static> Applicative for Writer<W> {
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let result = self.run_writer();
        let (value, log) = result.as_ref();
        let new_value = f(value.clone());
        Arc::new(Writer::new(new_value, log.clone())) as AnyBox
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let Some(b_writer) = b.downcast_ref::<Writer<W>>() {
            let (a_value, a_log) = &*(self.run)();
            let (b_value, b_log) = &*(b_writer.run)();
            
            Arc::new(Writer::new(
                f(a_value.clone(), b_value.clone()),
                a_log.combine(Arc::new(b_log.clone()) as AnyBox).downcast_ref::<W>().unwrap().clone()
            ))
        } else {
            Arc::new(self.clone())
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let (Some(b_writer), Some(c_writer)) = (b.downcast_ref::<Writer<W>>(), c.downcast_ref::<Writer<W>>()) {
            let (a_value, a_log) = &*(self.run)();
            let (b_value, b_log) = &*(b_writer.run)();
            let (c_value, c_log) = &*(c_writer.run)();
            
            let combined_log = a_log
                .combine(Arc::new(b_log.clone()) as AnyBox)
                .downcast_ref::<W>()
                .unwrap()
                .clone()
                .combine(Arc::new(c_log.clone()) as AnyBox)
                .downcast_ref::<W>()
                .unwrap()
                .clone();
            
            Arc::new(Writer::new(
                f(a_value.clone(), b_value.clone(), c_value.clone()),
                combined_log
            ))
        } else {
            Arc::new(self.clone())
        }
    }
}

impl<W: TypeOps + Semigroup + Monoid + Clone + Default + 'static> Monad for Writer<W> {
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let (value, log1) = &*(self.run)();
        if let Some(writer_b) = f(value.clone()).downcast_ref::<Writer<W>>() {
            let (b_value, log2) = &*(writer_b.run)();
            Arc::new(Writer::new(
                b_value.clone(),
                log1.combine(Arc::new(log2.clone()) as AnyBox).downcast_ref::<W>().unwrap().clone()
            ))
        } else {
            Arc::new(self.clone())
        }
    }

    fn join(&self) -> AnyBox {
        let (value, log1) = &*(self.run)();
        if let Some(inner_writer) = value.downcast_ref::<Writer<W>>() {
            let (inner_value, log2) = &*(inner_writer.run)();
            Arc::new(Writer::new(
                inner_value.clone(),
                log1.combine(Arc::new(log2.clone()) as AnyBox).downcast_ref::<W>().unwrap().clone()
            ))
        } else {
            Arc::new(self.clone())
        }
    }
}
