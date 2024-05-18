//! Quantum Layer abstraction
//!
//! Provides operations on the qubit layer, such as quantum operations
//!     and print utilities.

use num::pow;
use num::Complex;
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};
use std::fmt;
use std::sync::Mutex;

pub mod qasm_parser {
    pub struct ParsedInstruct {
        pub num_qubits: u32,
        pub ops: Vec<(u8, Vec<u32>)>,
    }

    pub fn parse(file_contents: &str) -> Result<ParsedInstruct, String> {
        // create a vector of strings split by newline
        let mut lines: Vec<String> = file_contents.split('\n').map(|s| s.to_owned()).collect();

        // remove all lines until qreg
        let mut remove_delim = 0;
        for line in &lines {
            if line.contains("qreg") {
                break;
            }
            remove_delim += 1;
            continue;
        }

        // Parse the number of qubits
        let num_qubits: String = lines[0].chars().filter(|&c| c.is_numeric()).collect();
        let num_qubits = match num_qubits.parse::<u32>() {
            Ok(x) => x,
            Err(_) => return Err("Failed to parse the number of qubits!".to_owned()),
        };

        // remove all lines before and including qreg
        lines.drain(0..remove_delim + 1);

        // Filter each newline
        let mut parsed_instructions: Vec<(u8, Vec<u32>)> = vec![];
        for line in &lines {
            let operation: &str = match line.split_whitespace().next() {
                Some(operation) => operation,
                None => continue,
            };

            // parse qubit target list
            let target_qubits: Vec<u32> = match operation {
                // fetch the only target qubit after the op string
                "x" | "y" | "z" | "h" => {
                    let filtered_line: String = line
                        .chars()
                        .filter(|&c| c.is_numeric() || c == ' ')
                        .collect();
                    let filtered_line: Vec<String> =
                        filtered_line.split(' ').map(|s| s.to_owned()).collect();
                    match filtered_line[1].parse::<u32>() {
                        Ok(x) => vec![x],
                        Err(_) => return Err("Failed to parse the target qubit!".to_owned()),
                    }
                }
                // TODO: fetch two target qubits after the op string cx and cz
                // TODO: fetch three target qubits after the op string ccx
                _ => {
                    // trace!("Skipping unknown operation {}", other);
                    continue;
                }
            };

            // parse operation codes
            let operation: u8 = match operation {
                "x" => 0,
                "y" => 1,
                "z" => 2,
                "h" => 3,
                other => return Err(format!("Operation Code {} not recognized!", other)),
            };

            parsed_instructions.push((operation, target_qubits))
        }

        Ok(ParsedInstruct {
            num_qubits,
            ops: parsed_instructions,
        })
    }
}

#[derive(Clone)]
pub struct QubitLayer {
    main: Vec<Complex<f64>>,
    parity: Vec<Complex<f64>>,
}

impl fmt::Debug for QubitLayer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut output = String::new();
        for index_main in 0..self.main.len() {
            output += &format!("state {:b} -> {1}\n", index_main, self.main[index_main]);
        }
        write!(f, "{}", output)
    }
}

impl fmt::Display for QubitLayer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut output = String::from("");
        for state in &self.main {
            let str = format!("{} {}", output, state);
            output = str;
        }
        output.remove(0);
        write!(f, "{}", output)
    }
}

impl QubitLayer {
    pub fn execute(&mut self, instructions: Vec<(u8, Vec<u32>)>) -> Result<(), String> {
        for (op, target_qubit) in instructions {
            match Some(op) {
                Some(0) => {
                    self.pauli_x(target_qubit[0]);
                }
                Some(1) => {
                    self.pauli_y(target_qubit[0]);
                }
                Some(2) => {
                    self.pauli_z(target_qubit[0]);
                }
                Some(3) => {
                    self.hadamard(target_qubit[0]);
                }
                other => {
                    return Err(format!("Unrecognized Operation {:?}", other).to_owned());
                }
            }
        }
        Ok(())
    }

    pub fn get_num_qubits(&self) -> u32 {
        self.main.len().ilog2()
    }

    pub fn get_size_of(&self) -> usize {
        self.main.len()
    }

    pub fn hadamard_par(&mut self, target_qubit: u32) {
        let hadamard_const = 1.0 / std::f64::consts::SQRT_2;
        let parity_mutex = Mutex::new(&mut self.parity);

        self.main
            .par_iter()
            .enumerate()
            .for_each(|(state, &main_value)| {
                if main_value != Complex::new(0.0, 0.0) {
                    if state & Self::mask(target_qubit as usize) != 0 {
                        parity_mutex.lock().unwrap()[state] -= hadamard_const * main_value;
                    } else {
                        parity_mutex.lock().unwrap()[state] += hadamard_const * main_value;
                    }
                }
            });

        self.main
            .par_iter()
            .enumerate()
            .for_each(|(state, &main_value)| {
                if main_value != Complex::new(0.0, 0.0) {
                    let target_state: usize = state ^ Self::mask(target_qubit as usize);
                    parity_mutex.lock().unwrap()[target_state] += hadamard_const * main_value;
                }
            });

        self.reset_parity_layer();
    }

    pub fn hadamard(&mut self, target_qubit: u32) {
        let hadamard_const = 1.0 / std::f64::consts::SQRT_2;
        for state in 0..self.main.len() {
            if self.main[state] != Complex::new(0.0, 0.0) {
                if state & Self::mask(target_qubit.try_into().unwrap()) != 0 {
                    self.parity[state] -= hadamard_const * self.main[state];
                } else {
                    self.parity[state] += hadamard_const * self.main[state];
                }
            }
        }
        for state in 0..self.main.len() {
            if self.main[state] != Complex::new(0.0, 0.0) {
                let target_state: usize = state ^ Self::mask(target_qubit.try_into().unwrap());
                self.parity[target_state] += hadamard_const * self.main[state];
            }
        }
        self.reset_parity_layer();
    }

    pub fn pauli_y(&mut self, target_qubit: u32) {
        for state in 0..self.main.len() {
            if self.main[state] != Complex::new(0.0, 0.0) {
                let target_state: usize = state ^ Self::mask(target_qubit.try_into().unwrap());
                // if |0>, scalar 1i applies to |1>
                // if |1>, scalar -1i
                // TODO: probabily room for optimization here
                if target_state & Self::mask(target_qubit.try_into().unwrap()) != 0 {
                    self.parity[target_state] = self.main[state] * Complex::new(0.0, 1.0);
                } else {
                    self.parity[target_state] = self.main[state] * Complex::new(0.0, -1.0);
                }
            }
        }
        self.reset_parity_layer();
    }

    pub fn pauli_y_par(&mut self, target_qubit: u32) {
        let parity_mutex = Mutex::new(&mut self.parity);
        self.main.par_iter().enumerate().for_each(|(state, value)| {
            if *value != Complex::new(0.0, 0.0) {
                let target_state: usize = state ^ Self::mask(target_qubit.try_into().unwrap());
                if target_state & Self::mask(target_qubit.try_into().unwrap()) != 0 {
                    parity_mutex.lock().unwrap()[target_state] = *value * Complex::new(0.0, 1.0);
                } else {
                    parity_mutex.lock().unwrap()[target_state] = *value * Complex::new(0.0, -1.0);
                }
            }
        });

        self.reset_parity_layer();
    }

    pub fn pauli_z(&mut self, target_qubit: u32) {
        for state in 0..self.main.len() {
            if self.main[state] != Complex::new(0.0, 0.0) {
                if state & Self::mask(target_qubit.try_into().unwrap()) != 0 {
                    self.parity[state] = -self.main[state];
                } else {
                    self.parity[state] = self.main[state];
                }
            }
        }

        self.reset_parity_layer();
    }

    pub fn pauli_z_par(&mut self, target_qubit: u32) {
        let parity_mutex = Mutex::new(&mut self.parity);
        self.main.par_iter().enumerate().for_each(|(state, value)| {
            if *value != Complex::new(0.0, 0.0) {
                if state & Self::mask(target_qubit.try_into().unwrap()) != 0 {
                    parity_mutex.lock().unwrap()[state] = -*value;
                } else {
                    parity_mutex.lock().unwrap()[state] = *value;
                }
            }
        });

        self.reset_parity_layer();
    }

    pub fn pauli_x(&mut self, target_qubit: u32) {
        for state in 0..self.main.len() {
            if self.main[state] != Complex::new(0.0, 0.0) {
                let mut target_state: usize = state;
                target_state ^= Self::mask(target_qubit.try_into().unwrap()); // flip bit 0
                self.parity[target_state] = self.main[state];
            }
        }

        self.reset_parity_layer();
    }

    pub fn pauli_x_par(&mut self, target_qubit: u32) {
        let parity_mutex = Mutex::new(&mut self.parity);
        self.main.par_iter().enumerate().for_each(|(state, value)| {
            if *value != Complex::new(0.0, 0.0) {
                let mut target_state: usize = state;
                target_state ^= Self::mask(target_qubit.try_into().unwrap()); // flip bit 0
                parity_mutex.lock().unwrap()[target_state] = *value;
            }
        });

        self.reset_parity_layer();
    }

    fn reset_parity_layer(&mut self) {
        // clone parity qubit layer to qubit layer
        // self.main = self.parity.clone();
        self.main.clone_from(&self.parity);

        // reset parity qubit layer with 0
        self.parity
            .iter_mut()
            .map(|x| *x = Complex::new(0.0, 0.0))
            .count();
    }

    pub fn measure_qubits(&self) -> MeasuredQubits {
        let num_qubits = self.get_num_qubits();
        let mut measured_qubits: Vec<f64> = vec![0.0; num_qubits.try_into().unwrap()];

        for index_main in 0..self.main.len() {
            if self.main[index_main] == Complex::new(0.0, 0.0) {
                continue;
            }
            for (index_measured_qubits, value) in measured_qubits.iter_mut().enumerate() {
                // check if the state has a bit in common with the measured_qubit index
                // does not matter which it is, thats why >= 1
                if (index_main & Self::mask(index_measured_qubits)) > 0 {
                    *value += pow(self.main[index_main].norm(), 2);
                }
            }
        }
        MeasuredQubits::new(measured_qubits)
    }

    fn mask(position: usize) -> usize {
        0x1usize << position
    }

    pub fn new(num_qubits: u32) -> Self {
        let mut _main = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        _main[0] = Complex::new(1.0, 0.0);

        Self {
            main: _main,
            parity: vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)],
        }
    }
}

pub struct MeasuredQubits {
    results: Vec<f64>,
}

impl MeasuredQubits {
    pub fn new(results: Vec<f64>) -> Self {
        MeasuredQubits { results }
    }
}

impl fmt::Display for MeasuredQubits {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut output = String::new();
        for index_measured_qubits in 0..self.results.len() {
            output += &format!(
                "Qubit {0} -> {1}\n",
                index_measured_qubits + 1,
                self.results[index_measured_qubits]
            );
        }
        write!(f, "{}", output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_measured_display_trait_print() {
        let q_layer: QubitLayer = QubitLayer::new(2);
        let results = q_layer.measure_qubits();
        let expected = "Qubit 1 -> 0\nQubit 2 -> 0\n";
        println!("{}", results);
        assert_eq!(expected, format!("{}", results));
    }

    #[test]
    fn test_display_trait_print() {
        let q_layer: QubitLayer = QubitLayer::new(2);
        let expected = "1+0i 0+0i 0+0i 0+0i";
        println!("{}", q_layer);
        assert_eq!(expected, format!("{}", q_layer));
    }

    #[test]
    fn test_debug_trait_print() {
        let q_layer: QubitLayer = QubitLayer::new(2);
        let expected = "state 0 -> 1+0i\nstate 1 -> 0+0i\nstate 10 -> 0+0i\nstate 11 -> 0+0i\n";
        println!("{:?}", q_layer);
        assert_eq!(expected, format!("{:?}", q_layer));
    }

    #[test]
    fn test_hadamard_par_simple() {
        let hadamard_const = 1.0 / std::f64::consts::SQRT_2;
        let num_qubits = 3;
        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.hadamard_par(0);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[0] = Complex::new(hadamard_const, 0.0);
        test_vec[1] = Complex::new(hadamard_const, 0.0);
        assert_eq!(test_vec, q_layer.main);

        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.hadamard_par(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[0] = Complex::new(hadamard_const, 0.0);
        test_vec[4] = Complex::new(hadamard_const, 0.0);
        assert_eq!(test_vec, q_layer.main);
        q_layer = QubitLayer::new(num_qubits);
        q_layer.hadamard_par(0);
        q_layer.hadamard_par(1);
        q_layer.hadamard_par(2);
        let test_vec = vec![Complex::new(pow(hadamard_const, 3), 0.0); 2_usize.pow(num_qubits)];
        assert_eq!(test_vec, q_layer.main);
    }

    #[test]
    fn test_pauli_z_par_simple() {
        let num_qubits = 3;
        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_z_par(0);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[0] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);

        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_z_par(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[0] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);
        q_layer = QubitLayer::new(num_qubits);
        q_layer.pauli_z_par(0);
        q_layer.pauli_z_par(1);
        q_layer.pauli_z_par(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[0] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);
    }

    #[test]
    fn test_pauli_y_par_simple() {
        let num_qubits = 3;
        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_y_par(0);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[1] = Complex::new(0.0, 1.0);
        assert_eq!(test_vec, q_layer.main);

        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_y_par(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[4] = Complex::new(0.0, 1.0);
        assert_eq!(test_vec, q_layer.main);
        q_layer = QubitLayer::new(num_qubits);
        q_layer.pauli_y_par(0);
        q_layer.pauli_y_par(1);
        q_layer.pauli_y_par(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[7] = Complex::new(0.0, -1.0);
        assert_eq!(test_vec, q_layer.main);
    }

    #[test]
    fn test_pauli_x_par_simple() {
        let num_qubits = 3;
        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_x_par(0);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[1] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);

        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_x_par(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[4] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);
        q_layer = QubitLayer::new(num_qubits);
        q_layer.pauli_x_par(0);
        q_layer.pauli_x_par(1);
        q_layer.pauli_x_par(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[7] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);
    }

    #[test]
    fn test_hadamard_simple() {
        let hadamard_const = 1.0 / std::f64::consts::SQRT_2;
        let num_qubits = 3;
        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.hadamard(0);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[0] = Complex::new(hadamard_const, 0.0);
        test_vec[1] = Complex::new(hadamard_const, 0.0);
        assert_eq!(test_vec, q_layer.main);

        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.hadamard(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[0] = Complex::new(hadamard_const, 0.0);
        test_vec[4] = Complex::new(hadamard_const, 0.0);
        assert_eq!(test_vec, q_layer.main);
        q_layer = QubitLayer::new(num_qubits);
        q_layer.hadamard(0);
        q_layer.hadamard(1);
        q_layer.hadamard(2);
        let test_vec = vec![Complex::new(pow(hadamard_const, 3), 0.0); 2_usize.pow(num_qubits)];
        assert_eq!(test_vec, q_layer.main);
    }

    #[test]
    fn test_pauli_z_simple() {
        let num_qubits = 3;
        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_z(0);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[0] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);

        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_z(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[0] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);
        q_layer = QubitLayer::new(num_qubits);
        q_layer.pauli_z(0);
        q_layer.pauli_z(1);
        q_layer.pauli_z(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[0] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);
    }

    #[test]
    fn test_pauli_y_simple() {
        let num_qubits = 3;
        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_y(0);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[1] = Complex::new(0.0, 1.0);
        assert_eq!(test_vec, q_layer.main);

        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_y(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[4] = Complex::new(0.0, 1.0);
        assert_eq!(test_vec, q_layer.main);
        q_layer = QubitLayer::new(num_qubits);
        q_layer.pauli_y(0);
        q_layer.pauli_y(1);
        q_layer.pauli_y(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[7] = Complex::new(0.0, -1.0);
        assert_eq!(test_vec, q_layer.main);
    }

    #[test]
    fn test_pauli_x_simple() {
        let num_qubits = 3;
        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_x(0);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[1] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);

        let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
        q_layer.pauli_x(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[4] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);
        q_layer = QubitLayer::new(num_qubits);
        q_layer.pauli_x(0);
        q_layer.pauli_x(1);
        q_layer.pauli_x(2);
        let mut test_vec = vec![Complex::new(0.0, 0.0); 2_usize.pow(num_qubits)];
        test_vec[7] = Complex::new(1.0, 0.0);
        assert_eq!(test_vec, q_layer.main);
    }
}
