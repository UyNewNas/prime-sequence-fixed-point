# A Self-Referential Fixed Point for the Sieve

**A Self-Referential Fixed Point for the Eratosthenes Sieve: Formally Verified in Lean 4**

This repository contains the complete **Lean 4** formalisation of the paper

## Overview

We prove that the sequence of prime numbers is the unique fixed point of 
a sieve functional Phi on the class of strictly increasing, indivisible sequences 
of positive integers. The functional Phi constructs a sequence by recursive 
Eratosthenean sieving: at each step, it selects the smallest integer exceeding 
the previous term that is not divisible by any earlier term. 

We show that Phi is in fact a constant functional -- for every admissible input 
sequence, Phi outputs the prime sequence p = (2, 3, 5, 7, ...). Consequently, 
the primes are characterised without circularity as the only strictly increasing, 
indivisible sequence closed under Phi.

We further introduce a sparse encoding Psi mapping such sequences to real numbers 
via Psi(S) = sum_{k=1}^{infinity} (S(k) mod 10) / 10^{k^2}, and prove that the 
Liouville-Erdos constant L is the unique real number whose decoded sequence is a 
fixed point of Phi, establishing L as a genuinely self-referential constant.

## Formalisation

The formalisation is divided into six modules:

| Module | File | Description |
|--------|------|-------------|
| M1a | `Common.lean` | Divisibility properties, strict monotonicity, Indivisible predicate |
| M1b | `PrimeDef.lean` | Definition of Prime, Euclid's lemma, existence of prime factors, `no_smaller_prime_dvd` |
| M2 | `SeqFixedPoint.lean` | GoodSeq structure, Phi functional, fixed-point predicate |
| M3 | `RealCoding.lean` | Axiomatic real numbers, series, Psi encoding map |
| M4 | `PrimeSieve.lean` | Prime sequence axioms, sieve characterisation, `next_prime_eq_min` |
| M5 | `MainProofs.lean` | Conjectures A, B, C (unique fixed point, self-referential constant, strong self-reference) |

## Building

Install Lean 4 (version 4.30.0-rc2 or compatible) and run:

```bash
lake build
```

All modules compile with zero `sorry` axioms.

## Project Structure

```
├── PrimeSequenceFixedPoint.lean          # Top-level module
├── PrimeSequenceFixedPoint/
│   ├── Common.lean              # M1a: Divisibility & basic properties
│   ├── PrimeDef.lean            # M1b: Prime definition & tests
│   ├── SeqFixedPoint.lean       # M2: Sequence structure & Phi
│   ├── RealCoding.lean          # M3: Real coding Psi
│   ├── PrimeSieve.lean          # M4: Core sieve lemma
│   └── MainProofs.lean          # M5: Conjectures A, B, C
├── lakefile.toml
├── lean-toolchain
├── LICENSE
└── README.md
```

## License

This project is released under the MIT License. See [LICENSE](LICENSE) for details.

## Citation

If you use this formalisation in your research, please cite the accompanying paper:

> Chan Slava. *The Prime Sequence as the Unique Fixed Point of a Self-Referential Functional*. Preprint, 2025.
