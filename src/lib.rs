pub mod coordinate_system;
pub mod day_setup;
pub mod graph;
pub mod grid;
pub mod math;
pub mod miscellaneous;

#[cfg(test)]
mod te {
    use crate::coordinate_system::Coordinate;
    use crate::grid::sized_grid::SizedGrid;
    use crate::miscellaneous::the_visitor::{TheVisitor, Timer};
    #[test]
    fn test() {
        let grid = SizedGrid::<Timer, 4, 4>::new(Timer::BLANK);

        let mut visitor = TheVisitor::new(grid);

        for _ in 0..u16::MAX {
            // Simulate a lot of clearing
            visitor.mark_visited(Coordinate::new(1, 1));
            assert!(visitor.has_visited(Coordinate::new(1, 1)));
            visitor.clear();
            assert!(!visitor.has_visited(Coordinate::new(1, 1)));
            visitor.clear();
        }
    }
}
