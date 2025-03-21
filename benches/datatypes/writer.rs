use criterion::{black_box, Criterion};
use rustica::datatypes::writer::Writer;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::monoid::Monoid;
use rustica::traits::pure::Pure;
use rustica::traits::semigroup::Semigroup;

// A log type for benchmarking Writer performance
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Log {
    _entries: Vec<String>,
}

impl Semigroup for Log {
    fn combine(&self, other: &Self) -> Self {
        let mut entries = self._entries.clone();
        entries.extend(other._entries.clone());
        Log { _entries: entries }
    }

    fn combine_owned(self, other: Self) -> Self {
        let mut entries = self._entries;
        entries.extend(other._entries);
        Log { _entries: entries }
    }
}

impl Monoid for Log {
    fn empty() -> Self {
        Log {
            _entries: Vec::new(),
        }
    }
}

// A different log type with a more compact representation
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CountLog {
    count: usize,
    message: String,
}

impl Semigroup for CountLog {
    fn combine(&self, other: &Self) -> Self {
        CountLog {
            count: self.count + other.count,
            message: format!("{} & {}", self.message, other.message),
        }
    }

    fn combine_owned(self, other: Self) -> Self {
        CountLog {
            count: self.count + other.count,
            message: format!("{} & {}", self.message, other.message),
        }
    }
}

impl Monoid for CountLog {
    fn empty() -> Self {
        CountLog {
            count: 0,
            message: String::new(),
        }
    }
}

pub fn writer_benchmarks(c: &mut Criterion) {
    // Section 1: Basic Creation and Access Operations
    let mut group = c.benchmark_group("Writer - Creation and Access");

    // Test creating a Writer with an empty log
    group.bench_function("new with empty log", |b| {
        b.iter(|| {
            black_box(Writer::<Log, i32>::new(Log::empty(), 42));
        });
    });

    // Test creating a Writer with a non-empty log
    group.bench_function("new with non-empty log", |b| {
        let log = Log {
            _entries: vec!["Entry 1".to_string(), "Entry 2".to_string()],
        };
        b.iter(|| {
            black_box(Writer::<Log, i32>::new(log.clone(), 42));
        });
    });

    // Test creating a Writer with the pure method
    group.bench_function("pure", |b| {
        b.iter(|| {
            black_box(Writer::<Log, i32>::pure(&42));
        });
    });

    // Test creating a Writer that only contains a log entry (no meaningful value)
    group.bench_function("tell with simple log", |b| {
        b.iter(|| {
            black_box(Writer::<Log, ()>::tell(Log {
                _entries: vec!["log entry".to_string()],
            }));
        });
    });

    group.bench_function("tell with complex log", |b| {
        let log = Log {
            _entries: vec![
                "Entry 1".to_string(),
                "Entry 2".to_string(),
                "Entry 3".to_string(),
                "Entry 4".to_string(),
                "Entry 5".to_string(),
            ],
        };
        b.iter(|| {
            black_box(Writer::<Log, ()>::tell(log.clone()));
        });
    });

    // Test extracting just the value from a Writer (doesn't evaluate log)
    group.bench_function("value extraction", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().value());
        });
    });

    // Test extracting just the log from a Writer
    group.bench_function("log extraction", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().log());
        });
    });

    // Test extracting both the log and value (run)
    group.bench_function("run (empty log)", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().run());
        });
    });

    group.bench_function("run (non-empty log)", |b| {
        let log = Log {
            _entries: vec!["Entry 1".to_string(), "Entry 2".to_string()],
        };
        let writer = Writer::<Log, i32>::new(log.clone(), 42);
        b.iter(|| {
            black_box(writer.clone().run());
        });
    });

    // Test with different log type
    group.bench_function("new with CountLog", |b| {
        let log = CountLog {
            count: 5,
            message: "Initial log".to_string(),
        };
        b.iter(|| {
            black_box(Writer::<CountLog, i32>::new(log.clone(), 42));
        });
    });

    group.bench_function("CountLog extraction", |b| {
        let log = CountLog {
            count: 5,
            message: "Initial log".to_string(),
        };
        let writer = Writer::<CountLog, i32>::new(log.clone(), 42);
        b.iter(|| {
            black_box(writer.clone().log());
        });
    });

    group.finish();

    // Section 2: Functor Operations
    let mut group = c.benchmark_group("Writer - Functor Operations");

    // Basic fmap with simple function
    group.bench_function("fmap simple operation", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().fmap(|x: &i32| x + 1));
        });
    });

    // fmap with more complex function
    group.bench_function("fmap complex operation", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().fmap(|x: &i32| {
                let mut result = 0;
                for i in 0..*x {
                    result += i;
                }
                result
            }));
        });
    });

    // fmap with type conversion
    group.bench_function("fmap type conversion", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().fmap(|x: &i32| x.to_string()));
        });
    });

    // fmap_owned with simple function
    group.bench_function("fmap_owned simple operation", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().fmap_owned(|x: i32| x + 1));
        });
    });

    // fmap with log
    group.bench_function("fmap with non-empty log", |b| {
        let log = Log {
            _entries: vec!["Entry 1".to_string(), "Entry 2".to_string()],
        };
        let writer = Writer::<Log, i32>::new(log.clone(), 42);
        b.iter(|| {
            black_box(writer.clone().fmap(|x: &i32| x * 2));
        });
    });

    // Chained fmap operations
    group.bench_function("fmap chained operations", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(
                writer
                    .clone()
                    .fmap(|x: &i32| x + 10)
                    .fmap(|x: &i32| x * 2)
                    .fmap(|x: &i32| x - 5),
            );
        });
    });

    group.finish();

    // Section 3: Applicative Operations
    let mut group = c.benchmark_group("Writer - Applicative Operations");

    // Apply with simple function
    group.bench_function("apply with simple function", |b| {
        let writer_fn = Writer::<Log, fn(&i32) -> i32>::new(Log::empty(), |x: &i32| x + 1);
        let writer_val = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer_val.clone().apply(&writer_fn));
        });
    });

    // Apply with function that has a log
    group.bench_function("apply with function having log", |b| {
        let log = Log {
            _entries: vec!["Function log".to_string()],
        };
        let writer_fn = Writer::<Log, fn(&i32) -> i32>::new(log.clone(), |x: &i32| x + 1);
        let writer_val = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer_val.clone().apply(&writer_fn));
        });
    });

    // Apply with value that has a log
    group.bench_function("apply with value having log", |b| {
        let writer_fn = Writer::<Log, fn(&i32) -> i32>::new(Log::empty(), |x: &i32| x + 1);
        let log = Log {
            _entries: vec!["Value log".to_string()],
        };
        let writer_val = Writer::<Log, i32>::new(log.clone(), 42);
        b.iter(|| {
            black_box(writer_val.clone().apply(&writer_fn));
        });
    });

    // Apply with both having logs
    group.bench_function("apply with both having logs", |b| {
        let fn_log = Log {
            _entries: vec!["Function log".to_string()],
        };
        let writer_fn = Writer::<Log, fn(&i32) -> i32>::new(fn_log.clone(), |x: &i32| x + 1);

        let val_log = Log {
            _entries: vec!["Value log".to_string()],
        };
        let writer_val = Writer::<Log, i32>::new(val_log.clone(), 42);

        b.iter(|| {
            black_box(writer_val.clone().apply(&writer_fn));
        });
    });

    // lift2 operation
    group.bench_function("lift2 with simple function", |b| {
        let writer1 = Writer::<Log, i32>::new(Log::empty(), 42);
        let writer2 = Writer::<Log, i32>::new(Log::empty(), 10);

        b.iter(|| {
            black_box(writer1.clone().lift2(&writer2, |x: &i32, y: &i32| x + y));
        });
    });

    // lift2 with logs
    group.bench_function("lift2 with both having logs", |b| {
        let log1 = Log {
            _entries: vec!["First log".to_string()],
        };
        let writer1 = Writer::<Log, i32>::new(log1.clone(), 42);

        let log2 = Log {
            _entries: vec!["Second log".to_string()],
        };
        let writer2 = Writer::<Log, i32>::new(log2.clone(), 10);

        b.iter(|| {
            black_box(writer1.clone().lift2(&writer2, |x: &i32, y: &i32| x + y));
        });
    });

    // lift3 operation
    group.bench_function("lift3 with simple function", |b| {
        let writer1 = Writer::<Log, i32>::new(Log::empty(), 42);
        let writer2 = Writer::<Log, i32>::new(Log::empty(), 10);
        let writer3 = Writer::<Log, i32>::new(Log::empty(), 5);

        b.iter(|| {
            black_box(
                writer1
                    .clone()
                    .lift3(&writer2, &writer3, |x: &i32, y: &i32, z: &i32| x + y + z),
            );
        });
    });

    // Apply owned
    group.bench_function("apply_owned", |b| {
        let writer_fn = Writer::<Log, fn(i32) -> i32>::new(Log::empty(), |x: i32| x + 1);
        let writer_val = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer_val.clone().apply_owned(writer_fn.clone()));
        });
    });

    group.finish();

    let mut group = c.benchmark_group("Writer");

    group.bench_function("bind", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(
                writer
                    .clone()
                    .bind(|x: &i32| Writer::<Log, i32>::new(Log::empty(), x + 1)),
            );
        });
    });

    group.finish();

    // Section 4: Monad Operations
    let mut group = c.benchmark_group("Writer - Monad Operations");

    // Basic bind operation
    group.bench_function("bind with simple function", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(
                writer
                    .clone()
                    .bind(|x: &i32| Writer::<Log, i32>::new(Log::empty(), x + 1)),
            );
        });
    });

    // Bind with adding log entries
    group.bench_function("bind with log adding function", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().bind(|x: &i32| {
                let log = Log {
                    _entries: vec![format!("Processed value: {}", x)],
                };
                Writer::<Log, i32>::new(log, x + 1)
            }));
        });
    });

    // Bind with conditional log entries
    group.bench_function("bind with conditional logging", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().bind(|x: &i32| {
                let log = if x % 2 == 0 {
                    Log {
                        _entries: vec!["Even number".to_string()],
                    }
                } else {
                    Log {
                        _entries: vec!["Odd number".to_string()],
                    }
                };
                Writer::<Log, i32>::new(log, *x + 1)
            }));
        });
    });

    // Chained bind operations
    group.bench_function("bind chained operations", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(
                writer
                    .clone()
                    .bind(|x: &i32| {
                        let log = Log {
                            _entries: vec!["First operation".to_string()],
                        };
                        Writer::<Log, i32>::new(log, x + 10)
                    })
                    .bind(|x: &i32| {
                        let log = Log {
                            _entries: vec!["Second operation".to_string()],
                        };
                        Writer::<Log, i32>::new(log, x * 2)
                    })
                    .bind(|x: &i32| {
                        let log = Log {
                            _entries: vec!["Third operation".to_string()],
                        };
                        Writer::<Log, i32>::new(log, x - 5)
                    }),
            );
        });
    });

    // Complex bind with type conversion
    group.bench_function("bind with type conversion", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().bind(|x: &i32| {
                let log = Log {
                    _entries: vec![format!("Converting {} to string", x)],
                };
                Writer::<Log, String>::new(log, x.to_string())
            }));
        });
    });

    // Bind with CountLog
    group.bench_function("bind with CountLog", |b| {
        let writer = Writer::<CountLog, i32>::new(CountLog::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().bind(|x: &i32| {
                let log = CountLog {
                    count: 1,
                    message: "Operation completed".to_string(),
                };
                Writer::<CountLog, i32>::new(log, x + 1)
            }));
        });
    });

    group.finish();

    // Section 5: Real-world Use Cases
    let mut group = c.benchmark_group("Writer - Real-world Use Cases");

    // Logging Computation Pipeline
    group.bench_function("logging computation pipeline", |b| {
        b.iter(|| {
            // Simple computation pipeline that logs each step
            let initial_writer = Writer::<Log, i32>::new(
                Log {
                    _entries: vec!["Starting computation".to_string()],
                },
                10,
            );

            black_box(
                initial_writer
                    .bind(|x: &i32| {
                        let log = Log {
                            _entries: vec![format!("Step 1: Input value is {}", x)],
                        };
                        Writer::<Log, i32>::new(log, x * 2)
                    })
                    .bind(|x: &i32| {
                        let log = Log {
                            _entries: vec![format!("Step 2: Input value is {}", x)],
                        };
                        Writer::<Log, i32>::new(log, x + 5)
                    })
                    .bind(|x: &i32| {
                        let log = Log {
                            _entries: vec![format!("Step 3: Input value is {}", x)],
                        };
                        Writer::<Log, i32>::new(log, x - 3)
                    })
                    .bind(|x: &i32| {
                        let log = Log {
                            _entries: vec![format!("Final result: {}", *x)],
                        };
                        Writer::<Log, i32>::new(log, *x)
                    }),
            );
        });
    });

    // Audit Trail for Financial Transactions
    group.bench_function("financial transaction audit trail", |b| {
        b.iter(|| {
            let initial_balance = 1000;
            let initial_writer = Writer::<Log, i32>::new(
                Log {
                    _entries: vec![format!("Initial balance: ${}", initial_balance)],
                },
                initial_balance,
            );

            black_box(
                initial_writer
                    .bind(|balance: &i32| {
                        // Deposit transaction
                        let amount = 500;
                        let new_balance = balance + amount;
                        let log = Log {
                            _entries: vec![format!(
                                "Deposit: ${} - New balance: ${}",
                                amount, new_balance
                            )],
                        };
                        Writer::<Log, i32>::new(log, new_balance)
                    })
                    .bind(|balance: &i32| {
                        // Withdrawal transaction
                        let amount = 200;
                        let new_balance = balance - amount;
                        let log = Log {
                            _entries: vec![format!(
                                "Withdrawal: ${} - New balance: ${}",
                                amount, new_balance
                            )],
                        };
                        Writer::<Log, i32>::new(log, new_balance)
                    })
                    .bind(|balance: &i32| {
                        // Fee transaction
                        let amount = 25;
                        let new_balance = balance - amount;
                        let log = Log {
                            _entries: vec![format!(
                                "Fee charged: ${} - New balance: ${}",
                                amount, new_balance
                            )],
                        };
                        Writer::<Log, i32>::new(log, new_balance)
                    }),
            );
        });
    });

    // Error Tracking in Data Processing
    group.bench_function("data processing with error tracking", |b| {
        b.iter(|| {
            // Process a list of values and track any processing errors
            let input_data = vec![10, 0, 5, -3, 8];
            let initial_writer = Writer::<Log, Vec<i32>>::new(
                Log {
                    _entries: vec!["Starting data processing".to_string()],
                },
                input_data.clone(),
            );

            black_box(
                initial_writer
                    .bind(|data: &Vec<i32>| {
                        // Process 1: Divide 100 by each value, track errors for division by zero
                        let mut result = Vec::new();
                        let mut log_entries = Vec::new();

                        for (i, &value) in data.iter().enumerate() {
                            if value == 0 {
                                log_entries
                                    .push(format!("Error at index {}: Cannot divide by zero", i));
                                result.push(0); // Placeholder value
                            } else {
                                result.push(100 / value);
                            }
                        }

                        let log = Log {
                            _entries: log_entries,
                        };
                        Writer::<Log, Vec<i32>>::new(log, result)
                    })
                    .bind(|data: &Vec<i32>| {
                        // Process 2: Ensure values are positive, log negatives
                        let mut result = Vec::new();
                        let mut log_entries = Vec::new();

                        for (i, &value) in data.iter().enumerate() {
                            if value < 0 {
                                log_entries.push(format!(
                                    "Warning at index {}: Negative value {}",
                                    i, value
                                ));
                                result.push(value.abs());
                            } else {
                                result.push(value);
                            }
                        }

                        let log = Log {
                            _entries: log_entries,
                        };
                        Writer::<Log, Vec<i32>>::new(log, result)
                    }),
            );
        });
    });

    // Event Sourcing System
    group.bench_function("event sourcing system", |b| {
        // Event sourcing for a simple shopping cart
        b.iter(|| {
            #[derive(Clone)]
            struct ShoppingCart {
                items: Vec<String>,
                total: f64,
            }

            let empty_cart = ShoppingCart {
                items: Vec::new(),
                total: 0.0,
            };
            let initial_writer = Writer::<Log, ShoppingCart>::new(
                Log {
                    _entries: vec!["Shopping cart created".to_string()],
                },
                empty_cart,
            );

            black_box(
                initial_writer
                    .bind(|cart: &ShoppingCart| {
                        // Add item event
                        let mut new_cart = cart.clone();
                        new_cart.items.push("Book".to_string());
                        new_cart.total += 15.99;

                        let log = Log {
                            _entries: vec!["Item added: Book - $15.99".to_string()],
                        };
                        Writer::<Log, ShoppingCart>::new(log, new_cart)
                    })
                    .bind(|cart: &ShoppingCart| {
                        // Add item event
                        let mut new_cart = cart.clone();
                        new_cart.items.push("Headphones".to_string());
                        new_cart.total += 49.99;

                        let log = Log {
                            _entries: vec!["Item added: Headphones - $49.99".to_string()],
                        };
                        Writer::<Log, ShoppingCart>::new(log, new_cart)
                    })
                    .bind(|cart: &ShoppingCart| {
                        // Remove item event
                        let mut new_cart = cart.clone();
                        if !new_cart.items.is_empty() {
                            let removed_item = new_cart.items.remove(0);
                            new_cart.total -= 15.99; // Price of the book

                            let log = Log {
                                _entries: vec![format!("Item removed: {}", removed_item)],
                            };
                            Writer::<Log, ShoppingCart>::new(log, new_cart)
                        } else {
                            let log = Log {
                                _entries: vec!["Cannot remove item: Cart is empty".to_string()],
                            };
                            Writer::<Log, ShoppingCart>::new(log, new_cart)
                        }
                    })
                    .bind(|cart: &ShoppingCart| {
                        // Apply discount event
                        let mut new_cart = cart.clone();
                        let discount = new_cart.total * 0.1;
                        new_cart.total -= discount;

                        let log = Log {
                            _entries: vec![format!("Discount applied: ${:.2}", discount)],
                        };
                        Writer::<Log, ShoppingCart>::new(log, new_cart)
                    }),
            );
        });
    });

    // System Configuration with Audit Trail
    group.bench_function("system configuration with audit", |b| {
        b.iter(|| {
            #[derive(Clone)]
            struct SystemConfig {
                max_connections: usize,
                debug_mode: bool,
                log_level: String,
            }
            
            let initial_config = SystemConfig {
                max_connections: 100,
                debug_mode: false,
                log_level: "INFO".to_string(),
            };
            
            let initial_writer = Writer::<Log, SystemConfig>::new(
                Log { _entries: vec!["Initial system configuration loaded".to_string()] }, 
                initial_config
            );
            
            black_box(
                initial_writer
                    .bind(|config: &SystemConfig| {
                        // Update max connections
                        let mut new_config = config.clone();
                        new_config.max_connections = 150;
                        
                        let log = Log { _entries: vec![format!("Max connections changed: {} -> {}", 
                            config.max_connections, new_config.max_connections)] };
                        Writer::<Log, SystemConfig>::new(log, new_config)
                    })
                    .bind(|config: &SystemConfig| {
                        // Enable debug mode
                        let mut new_config = config.clone();
                        new_config.debug_mode = true;
                        
                        let log = Log { _entries: vec![format!("Debug mode changed: {} -> {}", 
                            config.debug_mode, new_config.debug_mode)] };
                        Writer::<Log, SystemConfig>::new(log, new_config)
                    })
                    .bind(|config: &SystemConfig| {
                        // Change log level if debug mode is on
                        let mut new_config = config.clone();
                        if new_config.debug_mode {
                            new_config.log_level = "DEBUG".to_string();
                            
                            let log = Log { _entries: vec![format!("Log level changed: {} -> {}", 
                                config.log_level, new_config.log_level)] };
                            Writer::<Log, SystemConfig>::new(log, new_config)
                        } else {
                            let log = Log { _entries: vec!["No log level change: debug mode is off".to_string()] };
                            Writer::<Log, SystemConfig>::new(log, new_config)
                        }
                    })
            );
        });
    });

    // Logger Implementation
    group.bench_function("logger implementation", |b| {
        b.iter(|| {
            // Implement a simple logger using Writer
            let logger = Writer::<Log, ()>::tell(Log {
                _entries: vec!["Application started".to_string()],
            });

            black_box(
                logger
                    .bind(|_| {
                        // Log info message
                        let log = Log {
                            _entries: vec!["[INFO] User authentication started".to_string()],
                        };
                        Writer::<Log, ()>::tell(log)
                    })
                    .bind(|_| {
                        // Log info message
                        let log = Log {
                            _entries: vec!["[INFO] User authenticated successfully".to_string()],
                        };
                        Writer::<Log, ()>::tell(log)
                    })
                    .bind(|_| {
                        // Log warning message
                        let log = Log {
                            _entries: vec!["[WARNING] Session timeout set to default".to_string()],
                        };
                        Writer::<Log, ()>::tell(log)
                    })
                    .bind(|_| {
                        // Log error message
                        let log = Log {
                            _entries: vec![
                                "[ERROR] Database connection failed, retrying...".to_string()
                            ],
                        };
                        Writer::<Log, ()>::tell(log)
                    })
                    .bind(|_| {
                        // Log info message
                        let log = Log {
                            _entries: vec!["[INFO] Database connection established".to_string()],
                        };
                        Writer::<Log, ()>::tell(log)
                    }),
            );
        });
    });

    group.finish();
}
