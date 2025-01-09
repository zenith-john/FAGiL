# FAGiL (Foundations of Algebraic Geometry in Lean4)
[![Lean Action CI](https://github.com/zenith-john/FAGiL/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/zenith-john/FAGiL/actions/workflows/lean_action_ci.yml)

FAGiL consists of proof of theorems (proposition, lemmas, exercises ...) in [Foundations of Algebraic Geometry](https://math216.wordpress.com/) (currently, we use September 2024 version) by Ravi Vakil implemented in [Lean4](https://github.com/leanprover/lean4).

## Usage
The FAGiL is a standard lake package. So you can simply clone the repository and run
```
lake exe cache get
lake build
```

## Guidelines
We adopt the same [guideline](https://github.com/leanprover-community/mathlib4#guidelines) as [mathlib4](https://github.com/leanprover-community/mathlib4#guidelines), with following exceptions
- Naming convetion: we prefer to have an alias consistent with the book.
- Documentation style: Omit header comment unless you implement some theorem in a different way in the book Foundations of Algebraic Geometry.

## Dependencies
- [mathlib4](https://github.com/leanprover-community/mathlib4#guidelines)
