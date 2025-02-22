use crate::traits::hkt::AnyBox;
use std::sync::Arc;

/// Natural Transformation trait representing a functorial transformation between two type constructors.
/// Similar to Cats' ~> operator and Haskell's natural transformation concept.
pub trait NaturalTransformation: Send + Sync {
    /// Transform a value from functor F to functor G, preserving the structure.
    /// This is equivalent to Cats' FunctionK and Haskell's natural transformation.
    ///
    /// # Arguments
    /// * `fa` - A boxed value of the source functor F.
    ///
    /// # Returns
    /// A boxed value of the target functor G.
    fn transform(&self, fa: AnyBox) -> AnyBox;
}

/// Composed natural transformation.
pub struct ComposedNatural {
    /// First natural transformation to apply.
    f: Arc<dyn NaturalTransformation>,
    /// Second natural transformation to apply.
    g: Arc<dyn NaturalTransformation>,
}

impl ComposedNatural {
    /// Creates a new ComposedNatural from two natural transformations.
    ///
    /// # Arguments
    /// * `f` - The first natural transformation to apply.
    /// * `g` - The second natural transformation to apply.
    ///
    /// # Returns
    /// A new ComposedNatural instance.
    pub fn new(f: Arc<dyn NaturalTransformation>, g: Arc<dyn NaturalTransformation>) -> Self {
        ComposedNatural { f, g }
    }
}

impl NaturalTransformation for ComposedNatural {
    fn transform(&self, fa: AnyBox) -> AnyBox {
        let ga = self.f.transform(fa);
        self.g.transform(ga)
    }
}

/// Identity natural transformation.
#[derive(Clone)]
pub struct IdNat;

impl IdNat {
    /// Creates a new IdNat instance.
    ///
    /// # Returns
    /// A new IdNat instance.
    pub fn new() -> Self {
        IdNat
    }
}

impl NaturalTransformation for IdNat {
    fn transform(&self, fa: AnyBox) -> AnyBox {
        fa
    }
}

// Common natural transformations

/// Natural transformation from Option to Result.
pub struct OptionToResult;

impl NaturalTransformation for OptionToResult {
    fn transform(&self, fa: AnyBox) -> AnyBox {
        if let Some(opt) = fa.downcast_ref::<Option<AnyBox>>() {
            match opt {
                Some(x) => Arc::new(Ok::<AnyBox, AnyBox>(x.clone())),
                None => Arc::new(Err::<AnyBox, AnyBox>(Arc::new("None")))
            }
        } else {
            Arc::new(Err::<AnyBox, AnyBox>(Arc::new("Invalid type")))
        }
    }
}

/// Natural transformation from Result to Option.
pub struct ResultToOption;

impl NaturalTransformation for ResultToOption {
    fn transform(&self, fa: AnyBox) -> AnyBox {
        if let Some(res) = fa.downcast_ref::<Result<AnyBox, AnyBox>>() {
            match res {
                Ok(x) => Arc::new(Some(x.clone())),
                Err(_) => Arc::new(None::<AnyBox>)
            }
        } else {
            Arc::new(None::<AnyBox>)
        }
    }
}

/// Natural transformation from Vec to Option.
pub struct VecToOption;

impl NaturalTransformation for VecToOption {
    fn transform(&self, fa: AnyBox) -> AnyBox {
        if let Some(vec) = fa.downcast_ref::<Vec<AnyBox>>() {
            match vec.first() {
                Some(x) => Arc::new(Some(x.clone())),
                None => Arc::new(None::<AnyBox>)
            }
        } else {
            Arc::new(None::<AnyBox>)
        }
    }
}
