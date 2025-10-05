# lrm_sqim_cpu

[![CI](https://github.com/luisrmendes/lrm_sqim_cpu/actions/workflows/codeChecks.yml/badge.svg)](https://github.com/luisrmendes/lrm_sqim_cpu/actions/workflows/codeChecks.yml)
[![Security Audit](https://github.com/luisrmendes/lrm_sqim_cpu/actions/workflows/audit.yml/badge.svg)](https://github.com/luisrmendes/lrm_sqim_cpu/actions/workflows/audit.yml)
[![License](https://img.shields.io/badge/license-MIT_OR_Apache--2.0-blue.svg)](https://github.com/luisrmendes/lrm_sqim_cpu#license)
[![Cargo](https://img.shields.io/crates/v/lrm_sqim_cpu.svg)](https://docs.rs/lrm_sqim_cpu/0.1.0/lrm_sqim_cpu/)
[![Rust 1.67+](https://img.shields.io/badge/rust-1.67+-lightgray.svg)](
https://www.rust-lang.org)
[![Documentation](https://docs.rs/lrm_sqim_cpu/badge.svg)](https://docs.rs/lrm_sqim_cpu/0.1.0/lrm_sqim_cpu/)

This provides a quantum simulation abstraction tool to simulate quantum circuits.  
Uses the state vector simulation method.  
Memory consumption is 2 * 8 * 2<sup>`num_qubits`</sup> bytes. For example, simulating 25 qubits cost ~537 MB.  

The following gate operations are implemented:

- Pauli X gate
- Pauli Y gate
- Pauli Z gate
- Hadamard gate
