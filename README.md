# quantum_state_sim

[![CI](https://github.com/luisrmendes/quantum_state_sim/actions/workflows/codeChecks.yml/badge.svg)](https://github.com/luisrmendes/quantum_state_sim/actions/workflows/codeChecks.yml)
[![Security Audit](https://github.com/luisrmendes/quantum_state_sim/actions/workflows/audit.yml/badge.svg)](https://github.com/luisrmendes/quantum_state_sim/actions/workflows/audit.yml)

This provides a quantum simulation abstraction tool to simulate quantum circuits.  
Uses the state vector simulation method.  
Memory consumption is 2 * 8 * 2<sup>`num_qubits`</sup> bytes. For example, simulating 25 qubits cost ~537 MB.  

The following gate operations are implemented:

- Pauli X gate
- Pauli Y gate
- Pauli Z gate
- Hadamard gate
