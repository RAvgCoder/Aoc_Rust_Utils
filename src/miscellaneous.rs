use crate::grid::Grid;
use std::fmt::{Debug, Display};
use std::fs::File;
use std::io::Write;

// Give me a fn that dumps a grid to a file passing in the file name
pub fn dump_grid_to_file<T, F, M, G>(
    grid: &G,
    file_name: &str,
    own_func: Option<F>,
) -> std::io::Result<()>
where
    G: Grid<T> + Debug,
    F: Fn(&T) -> M,
    M: Display,
{
    dump_obj_to_file(file_name, |file| match &own_func {
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
    })
}

pub fn dump_obj_to_file<F>(file_name: &str, f: F) -> std::io::Result<()>
where
    F: Fn(&mut File) -> std::io::Result<()>,
{
    let mut file = File::create(file_name)?;
    f(&mut file)?;
    Ok(())
}
