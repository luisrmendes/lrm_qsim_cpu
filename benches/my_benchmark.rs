use criterion::*;
use quantum_layer::{self, QubitLayer};

fn bench_full_hadamard_24() {
    let num_qubits = 24;
    let mut q_layer: QubitLayer = QubitLayer::new(num_qubits);
    for it in 0..num_qubits - 1 {
        q_layer.hadamard(it);
    }
}

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("bench_full_hadamard_24", |b| {
        b.iter(|| bench_full_hadamard_24())
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = criterion_benchmark
}
criterion_main!(benches);
