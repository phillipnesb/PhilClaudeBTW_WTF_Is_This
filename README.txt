# BTW Abelian Sandpile Kernel (Zero-Dependency Lean 4)

A self-contained, zero-dependency Lean 4 formalization certifying finite termination, Abelian confluence, boundary integrity, and machine-level integer overflow immunity for the 2D Bak–Tang–Wiesenfeld (BTW) Abelian sandpile model.

The entire development relies strictly on Lean 4's core kernel primitives (`Nat`, `Int`, `omega`, `simp`, `decide`, `funext`) with **no external imports** (not even Mathlib).

## Quick Verification

Ensure you have a standard [Lean 4 toolchain](https://lean-lang.org) installed, then verify the kernel directly:

```bash
lean BTWSandpileVerified.lean
```

Zero output and exit code `0` confirm that every theorem and invariant passes the Lean 4 kernel without `sorry` or external axioms.

## Repository Contents

* **`BTWSandpileVerified.lean`** — Complete formal specification and proofs.
* **`Verification_Report.pdf`** — Summary report and theorem matrix *(rename to match your uploaded PDF filename)*.
* **`LICENSE`** — Public domain dedication (Unlicense).

## Formal Theorem & Certification Matrix

| Identifier | Theorem | Mathematical & Runtime Guarantee |
| :--- | :--- | :--- |
| **INV-1** | `invariant1_potential_bound` | Uniform single-cell harmonic weight bound: $h(r, c) \le \lfloor (N + 1)^2 / 2 \rfloor$. |
| **INV-2** | `invariant2_laplacian_exact`<br>`invariant2_superharmonic` | Separable 1D factorization proving $-\Delta h(r, c) = 4 + \text{boundaryExcess}(r, c) \ge 4$ everywhere on $\Omega = \{1, \dots, N\}^2$ without 16-way boundary case splits. |
| **INV-3** | `invariant3_abelian_commutativity` | Unconditional order-independence of single topplings at distinct sites. |
| **BISIM** | `batch_eq_iterated_topple` | Extensional equivalence between $k$-fold batch toppling (`toppleBatch`) and $k$ sequential topples. |
| **CERT-01** | `cert01_lyapunov_descent` | Exact energy-dissipation balance $\Psi_h(z_{\text{final}}) + 4S + \text{loss} = \Psi_h(z_{\text{init}})$ and universal termination bound $S \le \lfloor \Psi_h(z_{\text{init}}) / 4 \rfloor$. |
| **INV-4** | `invariant4_bitwise_equivalence` | Equivalence of bit-shift quotient/remainder operations (`v >>> 2 = v / 4`) for fast low-level kernels. |
| **CERT-02** | `cert02_dynamic_overflow_immunity` | Guarantees every interior and exterior cell remains strictly below $2^{62} - 1$ throughout any valid avalanche trace for $N \le 2^{29}$ and initial mass $\le 4N^2 + 1$. |
| **STAT-01** | `stat01_euler_maclaurin_bound` | Kernel-checked rational inequality for an analytical Euler–Maclaurin remainder bound via `decide`. |

## License

Dedicated to the public domain under [The Unlicense](LICENSE).
