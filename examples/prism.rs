//! Prism Usage Example
//!
//! Demonstrates bidirectional functional accessors (optics) for sum types:
//! - Selectively previewing (extracting) specific enum variants
//! - Reviewing (constructing) enum instances from variant payloads
//! - Modifying variant payloads with zero-cost moves
//! - Updating variant values via `set`
//! - Composing prisms to navigate and transform nested sum types

use rustica::datatypes::prism::Prism;

#[derive(Clone, Debug, PartialEq)]
enum TaskStatus {
    Queued,
    Running { progress: u8 },
    Completed(String),
    Failed { code: u16, reason: String },
}

#[derive(Clone, Debug, PartialEq)]
enum AppNotification {
    Task(TaskStatus),
    SystemAlert(String),
}

fn running_progress_prism()
-> Prism<TaskStatus, u8, impl Fn(&TaskStatus) -> Option<u8>, impl Fn(u8) -> TaskStatus> {
    Prism::new(
        |status: &TaskStatus| match status {
            TaskStatus::Running { progress } => Some(*progress),
            _ => None,
        },
        |progress: u8| TaskStatus::Running { progress },
    )
}

fn completed_result_prism()
-> Prism<TaskStatus, String, impl Fn(&TaskStatus) -> Option<String>, impl Fn(String) -> TaskStatus>
{
    Prism::new(
        |status: &TaskStatus| match status {
            TaskStatus::Completed(res) => Some(res.clone()),
            _ => None,
        },
        TaskStatus::Completed,
    )
}

fn notification_task_prism() -> Prism<
    AppNotification,
    TaskStatus,
    impl Fn(&AppNotification) -> Option<TaskStatus>,
    impl Fn(TaskStatus) -> AppNotification,
> {
    Prism::new(
        |notif: &AppNotification| match notif {
            AppNotification::Task(status) => Some(status.clone()),
            _ => None,
        },
        AppNotification::Task,
    )
}

fn main() {
    println!("=== Rustica Prism Example ===\n");

    let queued = TaskStatus::Queued;
    let running = TaskStatus::Running { progress: 45 };
    let completed = TaskStatus::Completed("Batch processing finished".to_string());
    let failed = TaskStatus::Failed {
        code: 500,
        reason: "Disk full".to_string(),
    };

    let progress_prism = running_progress_prism();
    let completed_prism = completed_result_prism();

    // Stage 1: Preview (Partial Extraction) and Review (Construction)
    println!("1. Preview and Review Operations:");
    assert_eq!(progress_prism.preview(&running), Some(45));
    assert_eq!(progress_prism.preview(&queued), None);
    assert_eq!(progress_prism.preview(&failed), None);
    println!("  Preview successfully extracted progress: Some(45)");
    println!("  Preview on non-matching variant safely returned None");

    let new_running = progress_prism.review(75);
    println!("  Reviewed new TaskStatus from progress: {:?}", new_running);
    assert_eq!(new_running, TaskStatus::Running { progress: 75 });

    let new_completed = completed_prism.review("Export complete".to_string());
    assert_eq!(
        new_completed,
        TaskStatus::Completed("Export complete".to_string())
    );

    println!();

    // Stage 2: Modifying Variant Payloads with Structural Sharing
    println!("2. Modifying Focused Variants:");
    let advanced = progress_prism.modify(running.clone(), |p| (p + 15).min(100));
    println!("  Advanced progress from 45 to: {:?}", advanced);
    assert_eq!(advanced, TaskStatus::Running { progress: 60 });

    // Modifying a non-matching variant is a safe no-op
    let untouched_queued = progress_prism.modify(queued, |p| p + 10);
    assert_eq!(untouched_queued, TaskStatus::Queued);
    println!("  Modifying mismatched variant leaves it unchanged.");

    // Identity modification preserves original structure
    let unchanged = progress_prism.modify(running.clone(), |p| p);
    assert_eq!(unchanged, running);
    println!("  Unchanged transformation utilizes structural sharing.");

    println!();

    // Stage 3: Updates via `set`
    println!("3. Updates via set:");
    let updated_running = progress_prism.set(running.clone(), 90);
    println!("  Updated running progress: {:?}", updated_running);
    assert_eq!(updated_running, TaskStatus::Running { progress: 90 });

    let still_completed = progress_prism.set(completed.clone(), 100);
    assert_eq!(still_completed, completed);
    println!("  Attempting to set absent variant returns original structure.");

    println!();

    // Stage 4: Composing Prisms with `then`
    println!("4. Composing Prisms for Deep Sum-Type Traversal:");
    // AppNotification -> TaskStatus -> progress
    let notification_progress_prism = notification_task_prism().then(running_progress_prism());

    let task_notif = AppNotification::Task(TaskStatus::Running { progress: 30 });
    let alert_notif = AppNotification::SystemAlert("Server maintenance scheduled".to_string());

    let extracted_progress = notification_progress_prism.preview(&task_notif);
    println!(
        "  Extracted nested progress from AppNotification: {:?}",
        extracted_progress
    );
    assert_eq!(extracted_progress, Some(30));

    assert_eq!(notification_progress_prism.preview(&alert_notif), None);
    println!("  Nested preview on mismatched outer variant safely returned None.");

    let updated_notif = notification_progress_prism.modify(task_notif, |p| p + 20);
    println!(
        "  Modified nested variant progress through composed prism: {:?}",
        updated_notif
    );
    assert_eq!(
        updated_notif,
        AppNotification::Task(TaskStatus::Running { progress: 50 })
    );

    let constructed_notif = notification_progress_prism.review(80);
    println!(
        "  Constructed deep structure via review: {:?}",
        constructed_notif
    );
    assert_eq!(
        constructed_notif,
        AppNotification::Task(TaskStatus::Running { progress: 80 })
    );

    println!("\n=== Prism Example Completed Successfully ===");
}
