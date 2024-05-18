use criterion::*;
use quantum_state_sim::{self, QuantumInstructions, QuantumOp, QubitLayer};

fn bench_full_hadamard_par_24() {
    let num_qubits = 24;
    let mut instructions: QuantumInstructions = vec![];
    for it in 0..num_qubits - 1 {
        instructions.push((QuantumOp::HadamardPar, it));
    }
    let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
    let _ = q_layer.execute(instructions);
}

fn bench_full_pauli_z_par_25() {
    let num_qubits = 25;
    let mut instructions: QuantumInstructions = vec![];
    for it in 0..num_qubits - 1 {
        instructions.push((QuantumOp::PauliZPar, it));
    }
    let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
    let _ = q_layer.execute(instructions);
}

fn bench_full_pauli_y_par_25() {
    let num_qubits = 25;
    let mut instructions: QuantumInstructions = vec![];
    for it in 0..num_qubits - 1 {
        instructions.push((QuantumOp::PauliYPar, it));
    }
    let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
    let _ = q_layer.execute(instructions);
}

fn bench_full_pauli_x_par_25() {
    let num_qubits = 25;
    let mut instructions: QuantumInstructions = vec![];
    for it in 0..num_qubits - 1 {
        instructions.push((QuantumOp::PauliXPar, it));
    }
    let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
    let _ = q_layer.execute(instructions);
}

fn bench_full_hadamard_24() {
    let num_qubits = 24;
    let mut instructions: QuantumInstructions = vec![];
    for it in 0..num_qubits - 1 {
        instructions.push((QuantumOp::Hadamard, it));
    }
    let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
    let _ = q_layer.execute(instructions);
}

fn bench_full_pauli_z_25() {
    let num_qubits = 25;
    let mut instructions: QuantumInstructions = vec![];
    for it in 0..num_qubits - 1 {
        instructions.push((QuantumOp::PauliZ, it));
    }
    let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
    let _ = q_layer.execute(instructions);
}

fn bench_full_pauli_y_25() {
    let num_qubits = 25;
    let mut instructions: QuantumInstructions = vec![];
    for it in 0..num_qubits - 1 {
        instructions.push((QuantumOp::PauliY, it));
    }
    let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
    let _ = q_layer.execute(instructions);
}

fn bench_full_pauli_x_25() {
    let num_qubits = 25;
    let mut instructions: QuantumInstructions = vec![];
    for it in 0..num_qubits - 1 {
        instructions.push((QuantumOp::PauliX, it));
    }
    let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
    let _ = q_layer.execute(instructions);
}

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("bench_full_pauli_z_25", |b| {
        b.iter(|| bench_full_pauli_z_25())
    });
    c.bench_function("bench_full_pauli_z_par_25", |b| {
        b.iter(|| bench_full_pauli_z_par_25())
    });
    c.bench_function("bench_full_pauli_x_25", |b| {
        b.iter(|| bench_full_pauli_x_25())
    });
    c.bench_function("bench_full_pauli_x_par_25", |b| {
        b.iter(|| bench_full_pauli_x_par_25())
    });
    c.bench_function("bench_full_pauli_y_25", |b| {
        b.iter(|| bench_full_pauli_y_25())
    });
    c.bench_function("bench_full_pauli_y_par_25", |b| {
        b.iter(|| bench_full_pauli_y_par_25())
    });
    c.bench_function("bench_full_hadamard_24", |b| {
        b.iter(|| bench_full_hadamard_24())
    });
    c.bench_function("bench_full_hadamard_par_24", |b| {
        b.iter(|| bench_full_hadamard_par_24())
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = criterion_benchmark
}
criterion_main!(benches);
