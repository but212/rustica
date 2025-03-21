#[cfg(feature = "advanced")]
use criterion::{black_box, Criterion};
#[cfg(feature = "advanced")]
use rustica::datatypes::state::State;
#[cfg(feature = "advanced")]
use rustica::datatypes::state::{get, put, modify};
#[cfg(feature = "advanced")]
use std::time::SystemTime;

// Define types for benchmarks
#[cfg(feature = "advanced")]
#[derive(Clone, Debug)]
struct LogEntry {
    timestamp: u64,
    level: String,
    message: String,
}

#[cfg(feature = "advanced")]
#[derive(Clone, Debug)]
struct FileReaderState {
    buffer: String,
    position: usize,
    last_read_time: SystemTime,
    logs: Vec<LogEntry>,
}

#[cfg(feature = "advanced")]
impl Default for FileReaderState {
    fn default() -> Self {
        FileReaderState {
            buffer: String::new(),
            position: 0,
            last_read_time: SystemTime::now(),
            logs: Vec::new(),
        }
    }
}

#[cfg(feature = "advanced")]
pub fn state_benchmarks(c: &mut Criterion) {
    // ======== BASIC OPERATIONS ========
    let mut group = c.benchmark_group("State - Basic Operations");

    group.bench_function("create_and_run", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s * 2, s + 1));
            black_box(state.run_state(5))
        });
    });

    group.bench_function("pure", |b| {
        b.iter(|| {
            let state = State::pure(42);
            black_box(state.run_state(1))
        });
    });

    group.bench_function("run_state", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s * 2, s + 1));
            black_box(state.run_state(10))
        });
    });

    group.finish();

    // ======== CORE OPERATIONS ========
    let mut group = c.benchmark_group("State - Core Operations");

    group.bench_function("eval_state", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s * 2, s + 1));
            black_box(state.eval_state(10))
        });
    });

    group.bench_function("exec_state", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s * 2, s + 1));
            black_box(state.exec_state(10))
        });
    });

    group.bench_function("get", |b| {
        b.iter(|| {
            let state = get::<i32>();
            black_box(state.run_state(10))
        });
    });

    group.bench_function("put", |b| {
        b.iter(|| {
            let state = put(42);
            black_box(state.run_state(10))
        });
    });

    group.bench_function("modify", |b| {
        b.iter(|| {
            let state = modify(|s: i32| s * 2);
            black_box(state.run_state(10))
        });
    });

    group.finish();

    // ======== FUNCTOR OPERATIONS ========
    let mut group = c.benchmark_group("State - Functor Operations");

    group.bench_function("fmap_simple", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s, s + 1));
            black_box(state.fmap(|x: i32| x * 2))
        });
    });

    group.bench_function("fmap_string", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s, s + 1));
            black_box(state.fmap(|x: i32| x.to_string()))
        });
    });

    group.bench_function("fmap_chain", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s, s + 1));
            black_box(state.fmap(|x: i32| x * 2).fmap(|x: i32| x + 1))
        });
    });

    group.finish();

    // ======== APPLICATIVE OPERATIONS ========
    let mut group = c.benchmark_group("State - Applicative Operations");

    group.bench_function("apply_pure", |b| {
        b.iter(|| {
            // Define a cloneable function object
            #[derive(Clone)]
            struct AddOne;
            impl AddOne {
                fn call(&self, x: i32) -> i32 { x + 1 }
            }
            
            // Create a computation that maps the AddOne function over a value
            let computation = State::pure(42).bind(|x| {
                State::pure(AddOne).bind(move |f| {
                    State::pure(f.call(x))
                })
            });
            
            black_box(computation.run_state(0))
        });
    });

    group.bench_function("apply_with_state", |b| {
        b.iter(|| {
            // Make the entire computation self-contained without external dependencies
            // This avoids the closure borrowing variables that don't live long enough
            let result = State::new(|s: i32| {
                // Define Adder inline to avoid any closure captures
                #[derive(Clone)]
                struct Adder(i32);
                impl Adder {
                    fn call(&self, x: i32) -> i32 { x + self.0 }
                }
                
                // Perform the entire computation within this closure
                let adder = Adder(s);
                let s1 = s + 1;  // State transition from add_state
                let val = s1 * 2; // Value from value_computation
                let s2 = s1 + 2;  // State transition from value_computation
                
                // Apply the adder to the value
                (adder.call(val), s2)
            });
            
            black_box(result.run_state(5))
        });
    });

    group.finish();

    // ======== MONAD OPERATIONS ========
    let mut group = c.benchmark_group("State - Monad Operations");

    group.bench_function("bind_simple", |b| {
        b.iter(|| {
            let state: State<i32, i32> = State::pure(42);
            black_box(state.bind(|x: i32| State::pure(x * 2)))
        });
    });

    

    group.bench_function("bind_chain", |b| {
        b.iter(|| {
            let state: State<i32, i32> = State::pure(42);
            black_box(
                state
                    .bind(|x: i32| State::pure(x * 2))
                    .bind(|x: i32| State::pure(x + 10))
            )
        });
    });

    group.finish();

    // ======== STATE CHAIN OPERATIONS ========
    let mut group = c.benchmark_group("State - Chain Operations");

    group.bench_function("get_put_chain", |b| {
        b.iter(|| {
            black_box(
                get::<i32>()
                    .bind(|s: i32| put(s * 2))
                    .bind(|_: ()| get::<i32>())
            )
        });
    });

    group.bench_function("complex_chain_with_conditionals", |b| {
        b.iter(|| {
            black_box(
                get::<i32>().bind(|s: i32| {
                    if s > 10 {
                        put(s * 2).bind(|_: ()| State::pure("large value"))
                    } else {
                        put(s + 5).bind(|_: ()| State::pure("small value"))
                    }
                })
            )
        });
    });

    group.bench_function("chain_with_statechange", |b| {
        b.iter(|| {
            // Create a chained State operation with state change
            let result = get::<i32>()
                .bind(|s: i32| {
                    let value = s;
                    // Create a state that modifies the state and returns the value
                    modify(move |state: i32| state + value)
                        .bind(move |_: ()| State::pure(value * 2))
                });

            black_box(result.run_state(5))
        });
    });

    group.bench_function("chain_with_intermediate_results", |b| {
        b.iter(|| {
            // Create a chained State operation that passes along intermediate results
            let result = get::<i32>()
                .bind(|s: i32| {
                    let original = s;
                    modify(move |state: i32| state * 2)
                        .bind(move |_: ()| get::<i32>()
                            .bind(move |new_s: i32| 
                                State::pure(format!("State changed from {} to {}", original, new_s))
                            )
                        )
                });

            black_box(result.run_state(5))
        });
    });

    group.bench_function("stack_push_pop", |b| {
        b.iter(|| {
            // Define a complete stack operation that manually threads state
            // to avoid any lifetime or borrowing issues
            let stack_operation = State::new(|stack: Vec<i32>| {
                // Push operations (fully implemented inline)
                let mut s1 = stack.clone();
                s1.push(1);
                
                let mut s2 = s1.clone();
                s2.push(2);
                
                let mut s3 = s2.clone();
                s3.push(3);
                
                // Pop operations
                let mut s4 = s3.clone();
                let x = s4.pop();
                
                let mut s5 = s4.clone();
                let y = s5.pop();
                
                // Return the final result
                ((x, y), s5)
            });
            
            black_box(stack_operation.run_state(Vec::new()))
        });
    });

    group.finish();

    // ======== REAL-WORLD USE CASES ========
    let mut group = c.benchmark_group("State - Counter/Accumulator");

    group.bench_function("increment_counter", |b| {
        b.iter(|| {
            let counter = modify(|s: i32| s + 1);
            black_box(counter.run_state(0))
        });
    });

    group.bench_function("accumulate_values", |b| {
        b.iter(|| {
            let values = vec![1, 2, 3, 4, 5];
            let result = values.iter().fold(
                State::pure(0),
                |state, val| {
                    let val = *val;
                    state.bind(move |current_val: i32| {
                        // Create a new state that accumulates the value
                        State::new(move |state: i32| {
                            let new_val = current_val + val;
                            let new_state = state + val;
                            (new_val, new_state)
                        })
                    })
                },
            );
            black_box(result.run_state(0))
        });
    });

    group.finish();

    let mut group = c.benchmark_group("State - Stack Operations");

    group.bench_function("calculator_operations", |b| {
        b.iter(|| {
            // Define a complete calculator operation that manually threads state
            // to avoid any lifetime or borrowing issues
            let calculator = State::new(|stack: Vec<i32>| {
                // Push 3 and 4
                let mut s1 = stack.clone();
                s1.push(3);
                
                let mut s2 = s1.clone();
                s2.push(4);
                
                // Pop twice to get operands
                let mut s3 = s2.clone();
                let x = s3.pop();
                
                let mut s4 = s3.clone();
                let y = s4.pop();
                
                // Compute result (addition)
                let result = match (x, y) {
                    (Some(a), Some(b)) => Some(a + b),
                    _ => None
                };
                
                // Push result back if it exists
                let s5 = match result {
                    Some(val) => {
                        let mut new_s = s4.clone();
                        new_s.push(val);
                        new_s
                    },
                    None => s4
                };
                
                (result, s5)
            });
            
            black_box(calculator.run_state(Vec::new()))
        });
    });

    group.finish();

    let mut group = c.benchmark_group("State - State Machine");

    group.bench_function("simple_state_transitions", |b| {
        // Define a simple state machine with states: Start -> Processing -> Complete
        #[derive(Clone, PartialEq, Debug)]
        enum MachineState {
            Start,
            Processing,
            Complete,
        }

        fn transition(input: char) -> State<MachineState, String> {
            State::new(move |state: MachineState| {
                match (state, input) {
                    (MachineState::Start, 'A') => (
                        "Moved to Processing".to_string(),
                        MachineState::Processing,
                    ),
                    (MachineState::Processing, 'B') => (
                        "Moved to Complete".to_string(),
                        MachineState::Complete,
                    ),
                    (state, _) => (
                        format!("Invalid transition from {:?}", state),
                        state,
                    ),
                }
            })
        }

        b.iter(|| {
            let machine = transition('A').bind(|result| {
                State::new(move |state: MachineState| {
                    if state == MachineState::Processing {
                        let next_result = transition('B').run_state(state);
                        (format!("{} -> {}", result, next_result.0), next_result.1)
                    } else {
                        (format!("{} (stopped)", result), state)
                    }
                })
            });

            black_box(machine.run_state(MachineState::Start))
        });
    });

    group.bench_function("document_processing_pipeline", |b| {
        #[derive(Clone, Debug)]
        struct Document {
            content: String,
            processed: bool,
            approved: bool,
        }

        // Define document processing steps
        fn process_content() -> State<Document, ()> {
            State::new(|mut doc: Document| {
                doc.content = doc.content.to_uppercase();
                doc.processed = true;
                ((), doc)
            })
        }

        fn approve_document() -> State<Document, bool> {
            State::new(|mut doc: Document| {
                doc.approved = doc.processed;
                (doc.approved, doc)
            })
        }

        b.iter(|| {
            let doc = Document {
                content: "draft document".to_string(),
                processed: false,
                approved: false,
            };

            let pipeline = process_content()
                .bind(|_: ()| approve_document())
                .bind(|approved: bool| {
                    State::new(move |doc: Document| {
                        let status = if approved {
                            "APPROVED"
                        } else {
                            "REJECTED"
                        };
                        (format!("Document status: {}", status), doc)
                    })
                });

            black_box(pipeline.run_state(doc))
        });
    });

    group.finish();

    let mut group = c.benchmark_group("State - Game State");

    group.bench_function("player_movement", |b| {
        #[derive(Clone, Debug)]
        struct GameState {
            player_x: i32,
            player_y: i32,
            steps: i32,
        }

        // Define movement functions
        fn move_player(dx: i32, dy: i32) -> State<GameState, (i32, i32)> {
            State::new(move |mut game: GameState| {
                game.player_x += dx;
                game.player_y += dy;
                game.steps += 1;
                ((game.player_x, game.player_y), game)
            })
        }

        b.iter(|| {
            let game = GameState {
                player_x: 0,
                player_y: 0,
                steps: 0,
            };

            let movements = move_player(1, 0)  // Right
                .bind(|_: (i32, i32)| move_player(0, 1))   // Down
                .bind(|_: (i32, i32)| move_player(1, 1))   // Diagonal
                .bind(|pos: (i32, i32)| {
                    State::new(move |game: GameState| {
                        (format!("Position: {:?}, Steps: {}", pos, game.steps), game)
                    })
                });

            black_box(movements.run_state(game))
        });
    });

    group.bench_function("game_loop_iteration", |b| {
        #[derive(Clone, Debug)]
        struct GameState {
            player_health: i32,
            enemy_health: i32,
            round: i32,
        }

        // Define game actions
        fn player_attack() -> State<GameState, i32> {
            State::new(|mut game: GameState| {
                let damage = 5 + (game.round % 3); // Varying damage
                game.enemy_health -= damage;
                (damage, game)
            })
        }

        fn enemy_attack() -> State<GameState, i32> {
            State::new(|mut game: GameState| {
                let damage = 3 + (game.round % 2); // Varying damage
                game.player_health -= damage;
                (damage, game)
            })
        }

        fn next_round() -> State<GameState, i32> {
            State::new(|mut game: GameState| {
                game.round += 1;
                (game.round, game)
            })
        }

        b.iter(|| {
            let game = GameState {
                player_health: 100,
                enemy_health: 50,
                round: 1,
            };

            // One complete game loop iteration
            let game_loop = player_attack()
                .bind(|player_dmg: i32| {
                    enemy_attack().bind(move |enemy_dmg: i32| {
                        next_round().bind(move |round: i32| {
                            State::new(move |game: GameState| {
                                let status = format!(
                                    "Round {}: Player dealt {} damage, Enemy dealt {} damage. Health P:{}/E:{}",
                                    round, player_dmg, enemy_dmg, game.player_health, game.enemy_health
                                );
                                (status, game)
                            })
                        })
                    })
                });

            black_box(game_loop.run_state(game))
        });
    });

    group.finish();

    let mut group = c.benchmark_group("State - Configuration Management");

    group.bench_function("feature_flag_toggle", |b| {
        #[derive(Clone, Debug)]
        struct Config {
            dark_mode: bool,
            notifications_enabled: bool,
            auto_save: bool,
        }

        // Define configuration operations
        fn toggle_feature(feature: &'static str) -> State<Config, bool> {
            State::new(move |mut config: Config| {
                match feature {
                    "dark_mode" => {
                        config.dark_mode = !config.dark_mode;
                        (config.dark_mode, config)
                    }
                    "notifications" => {
                        config.notifications_enabled = !config.notifications_enabled;
                        (config.notifications_enabled, config)
                    }
                    "auto_save" => {
                        config.auto_save = !config.auto_save;
                        (config.auto_save, config)
                    }
                    _ => (false, config),
                }
            })
        }

        b.iter(|| {
            let config = Config {
                dark_mode: false,
                notifications_enabled: true,
                auto_save: false,
            };

            let operations = toggle_feature("dark_mode")
                .bind(|dark_mode: bool| {
                    toggle_feature("auto_save").bind(move |auto_save: bool| {
                        State::new(move |config: Config| {
                            let summary = format!(
                                "Config updated: dark_mode={}, notifications={}, auto_save={}",
                                dark_mode, config.notifications_enabled, auto_save
                            );
                            (summary, config)
                        })
                    })
                });

            black_box(operations.run_state(config))
        });
    });

    group.bench_function("conditional_updates", |b| {
        #[derive(Clone, Debug)]
        struct Settings {
            theme: String,
            font_size: i32,
            volume: i32,
        }

        // Define configuration operations
        fn update_if_needed(field: &'static str, value: String) -> State<Settings, bool> {
            State::new(move |mut settings: Settings| {
                match field {
                    "theme" if settings.theme != value => {
                        settings.theme = value.clone();
                        (true, settings)
                    }
                    "font_size" => {
                        if let Ok(size) = value.parse::<i32>() {
                            if settings.font_size != size {
                                settings.font_size = size;
                                (true, settings)
                            } else {
                                (false, settings)
                            }
                        } else {
                            (false, settings)
                        }
                    }
                    "volume" => {
                        if let Ok(vol) = value.parse::<i32>() {
                            if settings.volume != vol {
                                settings.volume = vol;
                                (true, settings)
                            } else {
                                (false, settings)
                            }
                        } else {
                            (false, settings)
                        }
                    }
                    _ => (false, settings),
                }
            })
        }

        b.iter(|| {
            let settings = Settings {
                theme: "light".to_string(),
                font_size: 12,
                volume: 50,
            };

            let operations = update_if_needed("theme", "dark".to_string())
                .bind(|theme_changed: bool| {
                    update_if_needed("font_size", "14".to_string()).bind(move |font_changed: bool| {
                        update_if_needed("volume", "50".to_string()).bind(move |volume_changed: bool| {
                            State::new(move |settings: Settings| {
                                let changes = theme_changed as i32 + font_changed as i32 + volume_changed as i32;
                                let summary = format!(
                                    "Made {} changes. Current settings: theme={}, font_size={}, volume={}",
                                    changes, settings.theme, settings.font_size, settings.volume
                                );
                                (summary, settings)
                            })
                        })
                    })
                });

            black_box(operations.run_state(settings))
        });
    });

    group.finish();

    let mut group = c.benchmark_group("State - Logging System");

    group.bench_function("log_entry_appending", |b| {
        #[derive(Clone, Debug)]
        struct LogState {
            entries: Vec<String>,
            level: String,
        }

        // Define logging operations
        fn log(message: &'static str, level: &'static str) -> State<LogState, usize> {
            State::new(move |mut log_state: LogState| {
                let entry = format!("[{}] {}: {}", "timestamp", level, message);
                log_state.entries.push(entry);
                log_state.level = level.to_string();
                (log_state.entries.len(), log_state)
            })
        }

        b.iter(|| {
            let log_state = LogState {
                entries: Vec::new(),
                level: "INFO".to_string(),
            };

            let operations = log("Application started", "INFO")
                .bind(|_| log("Processing data", "INFO"))
                .bind(|_| log("Warning: resource usage high", "WARN"))
                .bind(|count: usize| {
                    State::new(move |log_state: LogState| {
                        let summary = format!("Logged {} entries. Last level: {}", count, log_state.level);
                        (summary, log_state)
                    })
                });

            black_box(operations.run_state(log_state))
        });
    });

    group.bench_function("log_filtering", |b| {
        #[derive(Clone, Debug)]
        struct LogSystem {
            entries: Vec<(String, String)>, // (level, message)
            min_level: usize,               // 0=DEBUG, 1=INFO, 2=WARN, 3=ERROR
        }

        // Define logging operations
        fn add_log(level: &'static str, message: &'static str) -> State<LogSystem, ()> {
            State::new(|mut logs: LogSystem| {
                logs.entries.push((level.to_string(), message.to_string()));
                ((), logs)
            })
        }

        fn filter_logs() -> State<LogSystem, Vec<(String, String)>> {
            State::new(|logs: LogSystem| {
                let level_priority = |level: &str| match level {
                    "DEBUG" => 0,
                    "INFO" => 1,
                    "WARN" => 2,
                    "ERROR" => 3,
                    _ => 0,
                };

                let filtered = logs
                    .entries
                    .iter()
                    .filter(|(level, _)| level_priority(level) >= logs.min_level)
                    .cloned()
                    .collect::<Vec<_>>();

                (filtered, logs)
            })
        }

        b.iter(|| {
            let log_system = LogSystem {
                entries: Vec::new(),
                min_level: 1, // INFO and above
            };

            let operations = add_log("DEBUG", "Detailed information")
                .bind(|_| add_log("INFO", "Normal operation"))
                .bind(|_| add_log("WARN", "Warning condition"))
                .bind(|_| add_log("ERROR", "Error condition"))
                .bind(|_| add_log("DEBUG", "More details"))
                .bind(|_| filter_logs())
                .bind(|filtered: Vec<(String, String)>| {
                    State::new(move |logs: LogSystem| {
                        let summary = format!(
                            "Filtered {} of {} logs (min_level={})",
                            filtered.len(),
                            logs.entries.len(),
                            logs.min_level
                        );
                        (summary, logs)
                    })
                });

            black_box(operations.run_state(log_system))
        });
    });

    group.bench_function("logging_system", |b| {
        b.iter(|| {
            // Define log entry creation with a fixed timestamp to avoid borrowing issues
            fn create_log_entry(level: &'static str, message: &'static str) -> LogEntry {
                LogEntry {
                    timestamp: 1647271234, // Use a fixed timestamp for benchmarking
                    level: level.to_string(),
                    message: message.to_string(),
                }
            }
            
            // Define a log append function
            fn append_log(level: &'static str, message: &'static str) -> State<FileReaderState, ()> {
                let entry = create_log_entry(level, message);
                State::new(move |mut state: FileReaderState| {
                    state.logs.push(entry.clone());
                    ((), state)
                })
            }
            
            // Create the log operations
            let log_operations = append_log("INFO", "Application started")
                .bind(|_| append_log("DEBUG", "Loading configuration"))
                .bind(|_| append_log("INFO", "Processing data"))
                .bind(|_| append_log("WARN", "Low memory detected"))
                .bind(|_| append_log("ERROR", "Failed to connect to database"))
                .bind(|_| State::new(|state: FileReaderState| {
                    let info_count = state.logs.iter().filter(|log| log.level == "INFO").count();
                    let error_count = state.logs.iter().filter(|log| log.level == "ERROR").count();
                    
                    // Also count messages containing specific text and average timestamp
                    let important_messages = state.logs.iter()
                        .filter(|log| log.message.contains("config"))
                        .count();
                    
                    let total_time: u64 = state.logs.iter()
                        .map(|log| log.timestamp)
                        .sum();
                    
                    let avg_time = if !state.logs.is_empty() {
                        total_time / state.logs.len() as u64
                    } else {
                        0
                    };
                    
                    (format!("Info: {}, Errors: {}, Important: {}, Avg time: {}", 
                             info_count, error_count, important_messages, avg_time), state)
                }));
                
            // Run the computation with an initial empty state
            black_box(log_operations.run_state(FileReaderState::default()))
        });
    });

    group.finish();

    let mut real_world_group = c.benchmark_group("State - Real World Computations");

    real_world_group.bench_function("state_computation", |b| {
        b.iter(|| {
            // Create a State computation that uses pattern matching
            let ops: State<i32, i32> = State::new(|s: i32| (s + 2, s * 3))
                .bind(|val: i32| {
                    State::new(move |s: i32| {
                        let result = if s > 10 { val * 2 } else { val + 10 };
                        (result, s / 2)
                    })
                });

            black_box(ops.run_state(5))
        });
    });

    real_world_group.bench_function("state_validation", |b| {
        b.iter(|| {
            // Create a state validation chain
            let validate_params = |x: i32, y: i32, z: i32| -> State<Vec<String>, bool> {
                State::new(move |mut errors: Vec<String>| {
                    let mut valid = true;
                    
                    if x < 0 {
                        errors.push("x must be non-negative".to_string());
                        valid = false;
                    }
                    
                    if y == 0 {
                        errors.push("y cannot be zero".to_string());
                        valid = false;
                    }
                    
                    if z > 100 {
                        errors.push("z must be <= 100".to_string());
                        valid = false;
                    }
                    
                    (valid, errors)
                })
            };

            black_box(validate_params(5, 10, 50).run_state(Vec::new()))
        });
    });

    real_world_group.bench_function("generic_operation_chain", |b| {
        b.iter(|| {
            // Define a generic operation chain
            fn start_state<S: Clone + 'static, T: Clone + 'static>(initial_value: T) -> State<S, T> {
                State::pure(initial_value)
            }

            let result: State<i32, String> = start_state("hello".to_string())
                .bind(|s: String| State::pure(format!("{} world", s)));

            black_box(result.run_state(42))
        });
    });

    real_world_group.bench_function("logger", |b| {
        b.iter(|| {
            // Define a logger state with fixed timestamp to avoid borrowing issues
            fn add_log_entry(level: &'static str, message: &'static str) -> State<Vec<LogEntry>, ()> {
                // Use a fixed timestamp to avoid borrowing issues
                let entry = LogEntry {
                    timestamp: 1647271234, // Fixed timestamp for benchmarking
                    level: level.to_string(),
                    message: message.to_string(),
                };
                
                modify(move |logs: Vec<LogEntry>| {
                    let mut new_logs = logs;
                    new_logs.push(entry.clone());
                    new_logs
                })
            }
            
            let logger = add_log_entry("INFO", "Application started")
                .bind(|_| add_log_entry("DEBUG", "Loading configuration"));
                
            black_box(logger.run_state(Vec::new()))
        });
    });

    real_world_group.bench_function("reader", |b| {
        b.iter(|| {
            // Define a reader state
            let reader: State<FileReaderState, String> = State::new(|mut reader: FileReaderState| {
                let content = reader.buffer.clone();
                reader.position += content.len();
                reader.last_read_time = SystemTime::now();
                (content, reader)
            });

            let initial_state = FileReaderState {
                buffer: "Hello, world!".to_string(),
                position: 0,
                last_read_time: SystemTime::now(),
                logs: Vec::new(),
            };

            black_box(reader.run_state(initial_state))
        });
    });

    real_world_group.finish();
}

#[cfg(not(feature = "advanced"))]
pub fn state_benchmarks(_c: &mut Criterion) {
    // No-op when feature is disabled
}
