# Lean 4 Formal Proof — Build & Verification Instructions

## Included Files
- `proof.lean` — The complete Lean 4 formalization with `#check` and `#print axioms` verification.
- `lakefile.lean` — Lake build configuration for standalone compilation.
- `lean-toolchain` — Specifies the Lean 4 toolchain version.

## How to Run & Verify
1. Ensure Lean 4 and `lake` are installed (via `elan`: https://github.com/leanprover/elan).
2. Place `proof.lean`, `lakefile.lean`, and `lean-toolchain` in the same directory.
3. Run standalone verification directly:
   ```bash
   lean proof.lean
   ```
4. Or build and execute the verified binary via Lake:
   ```bash
   lake build
   lake exe verify_proof
   ```
