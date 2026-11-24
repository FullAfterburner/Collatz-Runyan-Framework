# The Collatz–Runyan Framework

### Arithmetic Geometry, Modular Quantum Matter, and Induced Gravity

**Author:** Jake Thomas Runyan · Independent research programme  
**Edition:** Master Research Monograph, expanded edition — November 24, 2026  
**Status:** Exploratory research draft; not independently peer-reviewed.

## Overview

The Collatz–Runyan Framework investigates possible connections between discrete arithmetic, 2-adic dynamics, Pell equations, modular geometry, quantum matter and gravitation. Its long-term objective is to explore whether a common microscopic arithmetic quantum model can reproduce general relativity and consistent quantum matter in a controlled continuum limit.

The repository accompanies the 51-page Master Research Monograph and includes mathematical derivations, Python verification engines, archived numerical experiments, editable LaTeX source and an interactive 22-environment visualization suite. It documents negative results and limitations alongside successful mathematical benchmarks.

**This is a research programme, not an established unified physical theory.** It does not claim a proof of the Collatz conjecture or the Riemann hypothesis, a derivation of the Standard Model, or a prediction of the observed Newton constant or cosmological constant.

## Start here

- [Master Research Paper (PDF)](Collatz_Runyan_Master_Paper.pdf) — consolidated research, derivations, references and claim ledger.
- [Interactive 3D Visualization Suite v2.0](visualization/Collatz_Runyan_3D_Visualization_Suite_v2.html) — download the HTML and open it locally in a modern browser.
- [Master audit results](manuscript/master_audit_results.txt) — numerical recomputations and mass-splitting tests.
- [Previous monograph](historical/Collatz_Runyan_Research_Monograph.pdf) — historical research record.

## Research areas

| Area | Topics |
| --- | --- |
| Discrete arithmetic | Bernoulli numbers, Collatz trajectories, 2-adic valuations, Pell and Diophantine equations |
| Spectral geometry | Weighted-unitary dynamics, arithmetic mass operators, toroidal geometry |
| Modular quantum matter | Weil representations, Narain conformal field theories, modular bootstrap, A₄ flavor symmetry, complex multiplication |
| Particle physics | Neutrino and charged-lepton tests, modular Yukawa textures, topological chirality |
| Gravity and cosmology | Pell–Lorentz transformations, flux compactification, common effective actions, vacuum energy and induced gravity |
| Microscopic spacetime | Regge calculus, refinement criticality, causal triangulations, scalar determinant backreaction and continuum-limit tests |

## Selected mathematical and computational results

### Arithmetic and spectral foundations

The corrected standard Collatz trajectory of `305065927` takes **243 transitions** to reach 1. The earlier value of 114 is retained as an unresolved historical parameter, not a verified stopping time.

A symmetrized arithmetic matrix is

$$
A=\begin{pmatrix}3&\sqrt{185}\\ \sqrt{185}&17\end{pmatrix},\qquad
\lambda_\pm=10\pm\sqrt{234}.
$$

It gives the exact two-state transition amplitude-squared coefficient $185/234$. Interpreting the absolute eigenvalues as masses requires an additional physical hypothesis and an overall scale $M$:

$$
m_\pm=M(\sqrt{234}\pm10).
$$

The corresponding mass invariants are $m_-m_+=134M^2$ and $m_-^2+m_+^2=668M^2$. These identities do not identify the modes with observed particles.

### Selective quantum vacuum cancellation

For four real scalar degrees of freedom and one Dirac fermion with equal masses in each arithmetic sector, the free-field heat-kernel coefficients obey

$$
a_0=0,\qquad a_1=(1-4\xi)R,
$$

where $\xi$ is the scalar curvature coupling. At conformal coupling, $\xi=1/6$, the leading volume coefficient cancels while a nonzero Einstein–Hilbert contribution survives. The induced gravitational coupling remains dependent on the regulator, scale and assumed absence of a bare curvature term.

An alternative exact pairing of Kähler–Dirac and even-form determinants produces the topology-dependent weight

$$
W_{\mathrm{CR}}=[134(Ma)^2]^{-\chi},
$$

where $a$ is the lattice spacing and $\chi$ is the Euler characteristic. At fixed topology this weight cannot select local geometry. The expanded paper also derives a two-mass moment-rigidity result and quantifies regulated vacuum sensitivity to mass splitting.

### Quantum geometry and continuum tests

The ordered refinement-history ensemble satisfies $F(z)=1+zF(z)^5$, with exact critical activity $z_c=256/3125$. Despite the divergence of its mean volume, the sampled geometries exhibit branched-polymer-like scaling: effective Hausdorff dimension approximately 2.11 and spectral dimension approximately 1.35. They do not reproduce macroscopic four-dimensional spacetime.

On prescribed smooth four-dimensional backgrounds, Regge curvature and scalar kinetic-energy benchmarks exhibit approximately second-order convergence. Flat-lattice overlap fermion experiments also reproduce the expected Abelian topological index. These are necessary consistency tests, not evidence that dynamical Einstein gravity or the chiral Standard Model has emerged.

## Scientific status

| Result | Evidence / limitation |
| --- | --- |
| Corrected arithmetic and two-state spectrum | Exact within stated definitions |
| Modular representations and CFT constructions | Mathematical benchmarks using established methods |
| Arithmetic flux stabilization | Conditional local model; global consistency unresolved |
| Modular particle-mass predictions | Several minimal models fail experimental tests |
| Free-field vacuum cancellation and induced curvature | Conditional analytic results and numerical benchmarks |
| Refinement criticality | Exact for the restricted ordered-history ensemble |
| Dynamically emergent four-dimensional spacetime | Not obtained in tested ensembles |
| Absolute Newton constant and positive physical cosmological constant | Not derived |
| Interacting chiral Standard Model and UV-complete quantum gravity | Open research objectives |

## Repository structure

The paths below follow the expanded master research archive when extracted at the repository root.

```text
.
├── README.md
├── Collatz_Runyan_Master_Paper.pdf
├── manuscript/
│   ├── Collatz_Runyan_Master_Paper.tex
│   ├── master_audit.py
│   ├── master_audit_results.txt
│   ├── selective_rerun.txt
│   └── figures and previews
├── data/
│   ├── runyan_*.py
│   ├── runyan_*_results.txt
│   └── numerical JSON datasets
├── historical/
│   ├── Collatz_Runyan_Research_Monograph.pdf
│   ├── Collatz_Runyan_Research_Monograph.tex
│   └── Collatz_Runyan_Research_Archive.zip
└── visualization/
    ├── Collatz_Runyan_3D_Visualization_Suite_v2.html
    └── Collatz_Runyan_3D_Visualization_Source_v2.zip
```

## Reproduce the calculations

### Python environment

Use Python 3 and a virtual environment. From the repository root:

```bash
python -m venv .venv
```

Activate the environment:

```bash
# Linux / macOS
source .venv/bin/activate
```

```powershell
# Windows PowerShell
.venv\Scripts\Activate.ps1
```

Install the numerical and visualization dependencies:

```bash
python -m pip install numpy scipy sympy mpmath matplotlib plotly
```

### Run the master audit

```bash
python manuscript/master_audit.py
```

The audit reads the archived continuum and matter–geometry JSON datasets, checks exact mass-moment identities, recomputes selected statistics and regenerates figures. Compare its output with [`manuscript/master_audit_results.txt`](manuscript/master_audit_results.txt).

### Run individual experiments

```bash
# Modular bootstrap and common matter–gravity action
python data/runyan_modular_bootstrap_v03.py
python data/runyan_common_action_v01.py
python data/runyan_quantum_action_v02.py

# Continuum and chiral matter benchmarks
python data/runyan_controlled_continuum_v02.py
python data/runyan_overlap_index_v02.py

# Discrete geometry and quantum matter backreaction
python data/runyan_continuum_test.py
python data/runyan_matter_geometry_v03.py
python data/runyan_causal_matter_v04.py

# Selective vacuum cancellation with physical spinors
python data/runyan_selective_cancellation_v05.py
```

Some simulations may require substantial memory or computation time. Scripts may overwrite saved output files; run them on a working copy if you want to preserve the archival data. The master edition reran selected experiments and audited stored data, not every historical simulation. Exact dependency versions are not pinned in the current archive.

### Rebuild the monograph

With a standard TeX Live installation and the required LaTeX packages:

```bash
cd manuscript
pdflatex Collatz_Runyan_Master_Paper.tex
pdflatex Collatz_Runyan_Master_Paper.tex
pdflatex Collatz_Runyan_Master_Paper.tex
```

## Interactive visualization laboratory

![Causal geometry preview](manuscript/runyan_v2_causal_preview.png)

The [3D Visualization Suite](visualization/Collatz_Runyan_3D_Visualization_Suite_v2.html) contains 22 environments spanning arithmetic and modular geometry, particle-physics tests, criticality, matter–geometry crossover, causal triangulations and induced gravity. The self-contained HTML is designed to run offline; WebGL-compatible browsers enable interactive 3D views, and static fallbacks are provided.

## Research roadmap

- [x] Consolidate and correct the arithmetic and spectral foundations.
- [x] Develop modular quantum-matter and effective gravity benchmarks.
- [x] Test refinement criticality, matter backreaction and free-field cancellation.
- [ ] Implement physical spinorial matter on fluctuating causal triangulations.
- [ ] Establish a nonperturbative critical regime with extended four-dimensional scaling.
- [ ] Demonstrate a controlled continuum limit, unitarity and Einstein gravitational dynamics.
- [ ] Derive an anomaly-consistent interacting particle spectrum and regulator-independent physical predictions.

## Citation

If you use this work, please cite the master monograph and the relevant computational experiment.

> Runyan, Jake Thomas (2026). *The Collatz–Runyan Framework: Arithmetic Geometry, Modular Quantum Matter, and Induced Gravity*. Master Research Monograph, expanded edition, November 24, 2026. Research draft.

For archival citation, use the version-specific DOI from the corresponding Zenodo record once available. The DOI for this expanded edition has not been specified here.

## Feedback, provenance and licensing

Mathematical corrections, independent reproductions, constructive criticism and comparisons with established literature are welcome. Please distinguish analytical proofs, numerical benchmarks, modeling assumptions and open conjectures when reporting results.

The master edition includes AI-assisted technical synthesis and computational auditing; proposed constructions require author review and independent scientific scrutiny. References to established mathematical and physical methods are provided in the monograph.

No repository license is specified by this README. Consult the repository's `LICENSE` file if one is provided; otherwise obtain the author's permission for reuse beyond applicable legal rights.
