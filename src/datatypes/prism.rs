use std::sync::Arc;
use crate::prelude::*;

/// A Prism is an optic that focuses on a particular case of a sum type.
///
/// It consists of two functions:
/// - `preview`: Attempts to extract a value from the source type.
/// - `review`: Constructs a value of the source type.
///
/// # Example
///
/// ```
/// use std::sync::Arc;
/// use rustica::datatypes::prism::Prism;
/// use rustica::traits::hkt::AnyBox;
///
/// // Define an enum for demonstration
/// #[derive(Clone, Debug, PartialEq)]
/// enum Shape {
///     Circle(f64),
///     Rectangle(f64, f64),
/// }
///
/// // Create a Prism for the Circle case
/// let circle_prism = Prism::new(
///     Arc::new(|shape: Shape| -> Option<f64> {
///         match shape {
///             Shape::Circle(radius) => Some(radius),
///             _ => None,
///         }
///     }),
///     Arc::new(|radius: f64| -> Shape {
///         Shape::Circle(radius)
///     })
/// );
///
/// // Use the Prism
/// let circle = Arc::new(Shape::Circle(5.0)) as AnyBox;
/// let rectangle = Arc::new(Shape::Rectangle(4.0, 6.0)) as AnyBox;
///
/// assert!(circle_prism.preview(circle.clone()).is_some());
/// assert!(circle_prism.preview(rectangle.clone()).is_none());
///
/// let new_circle = circle_prism.review(Arc::new(7.0) as AnyBox);
/// assert_eq!(new_circle.downcast_ref::<Shape>(), Some(&Shape::Circle(7.0)));
/// ```
#[derive(Clone)]
pub struct Prism {
    preview: Arc<dyn Fn(AnyBox) -> Option<AnyBox> + Send + Sync>,
    review: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>,
}

impl Prism {
    /// Creates a new Prism.
    ///
    /// # Arguments
    ///
    /// * `preview` - A function that attempts to extract a value of type `B` from `A`.
    /// * `review` - A function that constructs a value of type `A` from `B`.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The source type.
    /// * `B`: The target type.
    pub fn new<A, B>(preview: Arc<dyn Fn(A) -> Option<B> + Send + Sync>, review: Arc<dyn Fn(B) -> A + Send + Sync>) -> Self
    where
        A: TypeOps + Clone + 'static,
        B: TypeOps + Clone + 'static,
    {
        Prism {
            preview: Arc::new(move |s: AnyBox| {
                s.downcast_ref::<A>().cloned().and_then(|a| {
                    preview(a).map(|b| Arc::new(b) as AnyBox)
                })
            }),
            review: Arc::new(move |b: AnyBox| {
                b.downcast_ref::<B>().cloned().map(|b| {
                    Arc::new(review(b)) as AnyBox
                }).unwrap_or(b)
            }),
        }
    }

    /// Attempts to extract a value from the source type.
    ///
    /// # Arguments
    ///
    /// * `s` - The source value.
    ///
    /// # Returns
    ///
    /// An `Option<AnyBox>` containing the extracted value if successful, or `None` if not.
    pub fn preview(&self, s: AnyBox) -> Option<AnyBox> {
        (self.preview)(s)
    }

    /// Constructs a value of the source type.
    ///
    /// # Arguments
    ///
    /// * `a` - The value to construct from.
    ///
    /// # Returns
    ///
    /// An `AnyBox` containing the constructed value.
    pub fn review(&self, a: AnyBox) -> AnyBox {
        (self.review)(a)
    }

    /// Creates a Prism for a specific case of a sum type.
    ///
    /// # Arguments
    ///
    /// * `match_case` - A function that matches a specific case of the sum type.
    /// * `make_case` - A function that constructs a value of the sum type from the case.
    ///
    /// # Type Parameters
    ///
    /// * `S`: The sum type.
    /// * `A`: The case type.
    ///
    /// # Returns
    ///
    /// A new `Prism` for the specified case.
    pub fn for_case<S, A>(
        match_case: impl Fn(S) -> Option<A> + Clone + Send + Sync + 'static,
        make_case: impl Fn(A) -> S + Clone + Send + Sync + 'static,
    ) -> Self
    where
        S: TypeOps + Clone + 'static,
        A: TypeOps + Clone + 'static,
    {
        let match_case = Arc::new(move |s| match_case(s)) as Arc<dyn Fn(S) -> Option<A> + Send + Sync>;
        let make_case = Arc::new(move |a| make_case(a)) as Arc<dyn Fn(A) -> S + Send + Sync>;
        Prism::new(match_case, make_case)
    }
}

impl Default for Prism {
    fn default() -> Self {
        Prism {
            preview: Arc::new(|x| Some(x)),
            review: Arc::new(|x| x),
        }
    }
}

impl HKT for Prism {
    fn apply_type(&self) -> AnyBox {
        Arc::new(self.clone()) as AnyBox
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<Prism>().map(|p| Arc::new(p.clone()) as AnyBox)
    }
}

impl Pure for Prism {
    fn pure(value: AnyBox) -> AnyBox {
        let value_clone = value.clone();
        Arc::new(Prism {
            preview: Arc::new(move |_| Some(value_clone.clone())),
            review: Arc::new(move |_| value.clone()),
        }) as AnyBox
    }
}

impl Functor for Prism {
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        Arc::new(Prism {
            preview: Arc::new({
                let preview = self.preview.clone();
                let f = f.clone();
                move |s| preview(s).map(|a| f(a))
            }),
            review: self.review.clone(),
        }) as AnyBox
    }
}

impl Applicative for Prism {
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        Arc::new(Prism {
            preview: Arc::new({
                let preview = self.preview.clone();
                move |s| {
                    preview(s).map(|a| f(a))
                }
            }),
            review: Arc::clone(&self.review)
        }) as AnyBox
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let Some(prism_b) = b.downcast_ref::<Prism>() {
            Arc::new(Prism {
                preview: Arc::new({
                    let preview_a = self.preview.clone();
                    let preview_b = prism_b.preview.clone();
                    let f = f.clone();
                    move |s| {
                        preview_a(s.clone()).and_then(|a| {
                            preview_b(s).map(|b| f(a, b))
                        })
                    }
                }),
                review: self.review.clone(),
            }) as AnyBox
        } else {
            Arc::new(self.clone()) as AnyBox
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let (Some(prism_b), Some(prism_c)) = (b.downcast_ref::<Prism>(), c.downcast_ref::<Prism>()) {
            Arc::new(Prism {
                preview: Arc::new({
                    let preview_a = self.preview.clone();
                    let preview_b = prism_b.preview.clone();
                    let preview_c = prism_c.preview.clone();
                    let f = f.clone();
                    move |s| {
                        preview_a(s.clone()).and_then(|a| {
                            preview_b(s.clone()).and_then(|b| {
                                preview_c(s).map(|c| f(a, b, c))
                            })
                        })
                    }
                }),
                review: self.review.clone(),
            }) as AnyBox
        } else {
            Arc::new(self.clone()) as AnyBox
        }
    }
}

impl Monad for Prism {
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        Arc::new(Prism {
            preview: Arc::new({
                let preview = self.preview.clone();
                let f = f.clone();
                move |s| {
                    let s_clone = s.clone();
                    preview(s_clone).and_then(|a| {
                        if let Some(prism) = f(a).downcast_ref::<Prism>() {
                            prism.preview(s)
                        } else {
                            None
                        }
                    })
                }
            }),
            review: self.review.clone(),
        }) as AnyBox
    }

    fn join(&self) -> AnyBox {
        Arc::new(Prism {
            preview: Arc::new({
                let preview = self.preview.clone();
                move |s| {
                    preview(s.clone()).and_then(|inner| {
                        if let Some(prism) = inner.downcast_ref::<Prism>() {
                            prism.preview(s)
                        } else {
                            None
                        }
                    })
                }
            }),
            review: self.review.clone(),
        }) as AnyBox
    }
}

impl Category for Prism {
    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        if let Some(other_prism) = other.downcast_ref::<Prism>() {
            Arc::new(Prism {
                preview: Arc::new({
                    let preview1 = self.preview.clone();
                    let preview2 = other_prism.preview.clone();
                    move |s| {
                        let s_clone = s.clone();
                        preview1(s).and_then(|_a| preview2(s_clone))
                    }
                }),
                review: self.review.clone(),
            }) as AnyBox
        } else {
            Arc::new(self.clone()) as AnyBox
        }
    }

    fn identity_morphism() -> AnyBox {
        Arc::new(Prism::default()) as AnyBox
    }
}

impl Arrow for Prism {
    fn arrow(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            Arc::new(Prism {
                preview: Arc::new({
                    let preview = self.preview.clone();
                    let func = func.clone();
                    move |s| preview(s).map(|a| func(a))
                }),
                review: self.review.clone(),
            }) as AnyBox
        } else {
            Arc::new(self.clone()) as AnyBox
        }
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            Arc::new(Prism {
                preview: Arc::new({
                    let preview = self.preview.clone();
                    let func = func.clone();
                    move |s| preview(s).map(|a| func(a))
                }),
                review: self.review.clone(),
            }) as AnyBox
        } else {
            Arc::new(self.clone()) as AnyBox
        }
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            Arc::new(Prism {
                preview: Arc::new({
                    let preview = self.preview.clone();
                    let func = func.clone();
                    move |s| preview(s).map(|a| func(a))
                }),
                review: self.review.clone(),
            }) as AnyBox
        } else {
            Arc::new(self.clone()) as AnyBox
        }
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        if let (Some(f_func), Some(g_func)) = (
            f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>(),
            g.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>()
        ) {
            Arc::new(Prism {
                preview: Arc::new({
                    let preview = self.preview.clone();
                    let f_func = f_func.clone();
                    let g_func = g_func.clone();
                    move |s| {
                        preview(s.clone()).map(|a| {
                            let f_result = f_func(a.clone());
                            let g_result = g_func(a);
                            Arc::new((f_result, g_result)) as AnyBox
                        })
                    }
                }),
                review: self.review.clone(),
            }) as AnyBox
        } else {
            Arc::new(self.clone()) as AnyBox
        }
    }
}

impl Identity for Prism {
    fn identity() -> AnyBox {
        Arc::new(Prism::default()) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Self::identity())
    }
}

impl Composable for Prism {
    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        self.fmap(f)
    }

    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x| {
            let f = Arc::clone(&f);
            let g = Arc::clone(&g);
            g(f(x))
        })
    }
}

impl Bifunctor for Prism {
    fn bimap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let preview = Arc::clone(&self.preview);
        let review = Arc::clone(&self.review);
        let f = Arc::clone(&f);
        let g1 = Arc::clone(&g);
        let g2 = Arc::clone(&g);
        Arc::new(Prism {
            preview: Arc::new(move |s: AnyBox| {
                preview(f(s.clone())).map(|a| g1(a))
            }),
            review: Arc::new(move |b: AnyBox| {
                review(g2(b.clone()))
            })
        }) as AnyBox
    }

    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        self.bimap(f, Arc::new(|x| x))
    }

    fn map_second(&self, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        self.bimap(Arc::new(|x| x), g)
    }
}

impl Foldable for Prism {
    fn fold_map(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let preview = Arc::clone(&self.preview);
        Arc::new(move |s: AnyBox| {
            match preview(s.clone()) {
                Some(a) => f(a),
                None => s
            }
        }) as AnyBox
    }

    fn fold_left(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let preview = Arc::clone(&self.preview);
        match preview(init.clone()) {
            Some(a) => f(init, a),
            None => init
        }
    }

    fn fold_right(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let preview = Arc::clone(&self.preview);
        match preview(init.clone()) {
            Some(a) => f(a, init),
            None => init
        }
    }
}

impl Traversable for Prism {
    fn traverse<F>(&self, f: Arc<F>) -> AnyBox 
    where 
        F: Fn(AnyBox) -> AnyBox + Send + Sync + 'static
    {
        Arc::new(Prism {
            preview: Arc::new({
                let preview = self.preview.clone();
                move |s| {
                    preview(s).map(|a| f(a))
                }
            }),
            review: Arc::clone(&self.review)
        }) as AnyBox
    }

    fn distribute(&self) -> AnyBox {
        let preview = Arc::clone(&self.preview);
        Arc::new(move |s: AnyBox| {
            match preview(s) {
                Some(a) => {
                    if let Some(inner_prism) = a.downcast_ref::<Prism>() {
                        Arc::new(inner_prism.clone()) as AnyBox
                    } else {
                        Arc::new(Prism::default()) as AnyBox
                    }
                },
                None => Arc::new(Prism::default()) as AnyBox
            }
        }) as AnyBox
    }
}