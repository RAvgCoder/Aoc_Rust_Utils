use crate::grid::Grid;
use std::fmt::{Debug, Display};
use std::fs::{File, OpenOptions};
use std::io::Write;

// Give me a fn that dumps a grid to a file passing in the file name
pub fn dump_grid_to_file<T, F, M, G>(
    grid: &G,
    file_name: Option<&str>,
    append: bool,
    own_func: Option<F>,
) -> std::io::Result<()>
where
    G: Grid<T> + Debug,
    F: Fn(&T) -> M,
    M: Display,
{
    dump_obj_to_file(
        Some(file_name.unwrap_or("grid_output.txt")),
        |file| match &own_func {
            Some(f) => {
                for row in 0..grid.num_rows() {
                    for e in grid.get_row(row).unwrap() {
                        write!(file, "{}", f(e))?;
                    }
                    writeln!(file)?;
                }

                Ok(())
            }
            None => {
                writeln!(file, "{:?}", grid)
            }
        },
        append,
    )
}

pub fn dump_obj_to_file<F>(file_name: Option<&str>, f: F, append: bool) -> std::io::Result<()>
where
    F: Fn(&mut File) -> std::io::Result<()>,
{
    let mut file = OpenOptions::new()
        .write(true)
        .append(append)
        .create(true) // Creates the file if it doesn't exist
        .open(file_name.unwrap_or("obj_dump.txt"))
        .expect("Unable to open or create the file");
    f(&mut file)?;
    Ok(())
}
