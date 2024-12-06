use std::env;
use std::fmt::Debug;
use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::time::{Duration, Instant};

/// Utility struct containing various helper functions.
pub struct Utils;

impl Utils {

    /// Executes a function with a single input and measures its execution time.
    ///
    /// # Arguments
    ///
    /// * `day_func_part_to_run` - The function to be executed.
    /// * `part_num` - The part number of the puzzle.
    /// * `day_num` - The day number of the puzzle.
    /// * `expected` - The expected result for assertion.
    ///
    /// # Type Parameters
    ///
    /// * `T` - The type of the input to the function. Must implement the `From<Vec<String>>` trait.
    /// * `F` - The function type that takes an input of type `T` and returns a result of type `R`.
    /// * `R` - The type of the result returned by the function. Must implement the `Debug` and `PartialEq` traits.
    ///
    /// # Panics
    ///
    /// This function will panic if the expected result does not match the actual result.
    ///
    /// # Examples
    ///
    /// ```example
    /// use aoc_utils_rust::day_setup::Utils;
    ///
    /// fn example_func(input: Vec<String>) -> usize {
    ///     input.len()
    /// }
    ///
    /// Utils::run_part_single(example_func, 1, 1, Some(3));
    /// ```
    pub fn run_part_single<T, F, R>(
        day_func_part_to_run: F,
        part_num: i32,
        day_num: u8,
        expected: Option<R>,
    ) where
        F: FnOnce(T) -> R,
        T: From<Vec<String>>,
        R: Debug + PartialEq,
    {
        println!(
            "//------------[Day {} Part {}]------------\\\\",
            day_num, part_num
        );

        let read_file = Self::read_file::<String>(day_num);
        let (parsing_time, final_type) = Self::time_it(move || T::from(read_file));
        println!(
            "Time taken to parse: {:?}",
            Self::log_elapsed_time(parsing_time)
        );

        let (elapsed_time, result) = Self::time_it(move || day_func_part_to_run(final_type));

        Self::log_results(expected, result, elapsed_time);

        println!(
            "Total time taken: {:?}",
            Self::log_elapsed_time(parsing_time + elapsed_time)
        );
    }

    fn time_it<R, F>(func: F) -> (Duration, R)
    where
        F: FnOnce() -> R,
    {
        let start_time = Instant::now();
        let result = func();
        let elapsed_time = start_time.elapsed();
        (elapsed_time, result)
    }

    /// Logs the results of a function execution, including the expected result, actual result, and execution time.
    ///
    /// # Arguments
    ///
    /// * `expected` - The expected result for assertion. If `None`, the result is considered incomplete.
    /// * `result` - The actual result obtained from the function execution.
    /// * `elapsed_time` - The duration of time taken to execute the function.
    ///
    /// # Type Parameters
    ///
    /// * `R` - The type of the result. Must implement the `Debug` and `PartialEq` traits.
    ///
    /// # Panics
    ///
    /// This function will panic if the actual result does not match the expected result.
    fn log_results<R>(expected: Option<R>, result: R, elapsed_time: Duration)
    where
        R: Debug + PartialEq,
    {
        // The assumption is that no advent of code answer is to ever be zero cuz that'll be boring
        match expected {
            None => println!("INCOMPLETE | Temp Result: {:?}", result),
            Some(expected) => {
                if result != expected {
                    println!(
                        r#"
Assertion Failed
----------------
Expected: {:?}
Found: {:?}
            "#,
                        expected, result
                    );
                    std::process::exit(1);
                }

                println!(
                    "Result: {:?}\t| Time Taken: {}",
                    result,
                    Self::log_elapsed_time(elapsed_time)
                );
            }
        }
    }

    fn log_elapsed_time(elapsed_time: Duration) -> String {
        // Convert to minutes, seconds, milliseconds, and microseconds
        let minutes = elapsed_time.as_secs() / 60;
        let secs = elapsed_time.as_secs() % 60;
        let millis = elapsed_time.as_millis() % 1_000;
        let micros = elapsed_time.as_micros() % 1_000; // Remaining microseconds after converting to milliseconds

        if minutes > 0 {
            format!(
                "{} minutes, {} secs, {} millis, and {} micros",
                minutes, secs, millis, micros
            )
        } else if secs > 0 {
            format!("{} secs, {} millis, and {} micros", secs, millis, micros)
        } else {
            format!("{} millis and {} micros", millis, micros)
        }
    }

    /// Reads a file and returns its content as a vector of elements of type `T`.
    ///
    /// # Arguments
    /// * `day_num` - The day number of the puzzle.
    ///
    /// # Type Parameters
    /// * `T` - The type of the elements in the input file.
    ///
    /// # Returns
    /// * `Vec<T>` - A vector containing the parsed elements from the file.
    ///
    /// # Panics
    ///  If the file cannot be opened or if parsing an element fails.
    fn read_file<T>(day_num: u8) -> Vec<T>
    where
        T: std::str::FromStr,
        T::Err: Debug,
    {
        let file_path = Self::get_file_path()
            .join("inputs")
            .join(if day_num == 0 {
                "Example".to_string()
            } else {
                format!("day{}", day_num)
            })
            .with_extension("txt");

        let file = File::open(&file_path)
            .unwrap_or_else(|_| panic!("Failed to open file at {}", file_path.display()));
        let reader = BufReader::new(file);
        reader
            .lines()
            .map(|line| line.unwrap().parse::<T>().unwrap())
            .collect()
    }

    /// Retrieves the base directory for the project.
    ///
    /// # Returns
    /// * `PathBuf` - The path to the project's base directory.
    fn get_file_path() -> PathBuf {
        let mut current_directory = env::current_dir().unwrap();

        if !current_directory.ends_with("src") {
            current_directory.push("src");
        }

        current_directory
    }

    /// Creates a new Rust file for a specific day with a template.
    ///
    /// # Arguments
    /// * `day_num` - The day number for which to create the new file.
    ///
    /// # Panics
    /// If the file already exists or if it cannot be created.
    pub fn new_day(day_num: i32, year: i16) {
        let src_file_path = Self::get_file_path()
            .join(format!("day{}", day_num))
            .with_extension("rs");
        if src_file_path.exists() {
            panic!(
                "Cannot create file as it already exists at {}",
                src_file_path.display()
            );
        }
        let input_file_path = Self::get_file_path()
            .join("inputs")
            .join(format!("day{}.txt", day_num));
        if input_file_path.exists() {
            panic!(
                "Cannot create file as it already exists at {}",
                input_file_path.display()
            );
        }
        println!("NEW_DAY.txt: {}", input_file_path.display());
        println!("    src.rs: {}", src_file_path.display());
        let _ = File::create(&input_file_path)
            .unwrap_or_else(|_| panic!("Failed to create file at {}", input_file_path.display()));
        let mut file = File::create(&src_file_path)
            .unwrap_or_else(|_| panic!("Failed to create file at {}", src_file_path.display()));
        writeln!(
            file,
            r#"
use aoc_utils_rust::day_setup::Utils;

/// Runs the Advent of Code puzzles for [Current Day](https://adventofcode.com/20{}/day/{}).
///
/// This function calls the `run_part` function from the `Utils` module to execute and time
/// the solutions for both parts of the current day, checking them against the expected results.
///
/// # Panics
///   If the result of any part does not match the expected value.
pub fn run() {{
    // run_part(day_func_part_to_run, part_num, day_num)
    Utils::run_part_single(part1, 1, 0, None);
    Utils::run_part_single(part2, 2, 0, None);
}}

fn part1(input: Vec<String>) -> u64 {{
    println!("Part 1: {{:#?}}", input);
    0
}}

fn part2(input: Vec<String>) -> u64 {{
    println!("Part 2 {{:#?}}", input);
    0
}}
                "#,
            year, day_num
        )
        .expect("Failed to write to file");
        println!(
            "File successfully created at location: {} & {}",
            src_file_path.display(),
            input_file_path.display()
        );
    }
}
