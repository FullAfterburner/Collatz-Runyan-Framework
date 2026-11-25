# Collatz–Runyan Lean Proofs — initial v2.2 formalization

**Build status at publication: uncompiled draft.** Lean was unavailable in the authoring environment. Do not describe this project as machine-verified until the pinned toolchain completes a successful build. This is a partial formalization of the mathematical core, not a formal proof of the entire framework.

Source manuscript: [Theorems, Supporting Lemmas and Complete Proofs (v2.1L)](../Proofs/Collatz_Runyan_Theorems_Lemmas_Proofs_v21L.pdf).

## Scope

| Module | Formal statements | Not yet formalized |
| --- | --- | --- |
| Arithmetic | Rational inverse maps, affine commutator, conditional Diophantine descent inequality, integer Pell examples | 2-adic representation and parity iteration identity |
| BranchAlgebra | Matrix-unit multiplication from equal-length cancellation | Haar measure, isometries, adjoints, independence, full algebra isomorphism |
| Lorentzian | Polynomial determinant and boost identity | Hermitian space dimension/signature theorem and full Lorentz group |
| Intersection | Zero complementary pairing for arbitrary integer vectors supported on four admissible triples | Radical independence, Lagrangian/calibration constraints, topology-to-coordinate identification |
| Pending | — | Circle orbit and Gromov–Hausdorff limit, quantum oscillator sums and Casimir limit |

In particular, the finite intersection result does not itself prove the full special Lagrangian theorem. No physical theory, Collatz convergence, or emergent spacetime is proved by this project.

## Build locally

Install Lean 4 using the [official installation instructions](https://lean-lang.org/install/). From the repository root:

```sh
cd "Lean Proofs"
lake update
lake exe cache get
lake build
```

The Lean and Mathlib versions are pinned to v4.19.0. The first build downloads dependencies. Commit the generated lake-manifest.json after confirming the dependency resolution. Open the folder in VS Code with the Lean 4 extension for interactive proof checking.

Check that the build exits successfully; inspect all diagnostics. To examine theorem dependencies in a Lean file, use for example:

```lean
import CollatzRunyan
#print axioms CollatzRunyan.supported_pairing_zero
#print axioms CollatzRunyan.affine_commutator
```

No unfinished proof placeholders or user-declared axioms are included in the initial source. This is not a guarantee that the source compiles, nor a claim that standard Mathlib foundations use no axioms. Any build errors should be corrected before labeling the statements machine-checked.

## Verification roadmap

1. Compile and review every initial theorem.
2. Formalize parity cylinders and branch isometries.
3. Formalize the exact cycle period and metric limit.
4. Formalize Fourier oscillator sums and the renormalized limit.
5. Prove the arithmetic radical independence and connect differential-form constraints to the integral homology pairing.

Keep the PDF, computational audits and Lean statements versioned separately. A successful build certifies only the statements actually expressed in Lean, under their explicit hypotheses.
