# Lean development

Conditional symmetry results for compact connected positive
quaternionic-Kähler manifolds, using Lean 4.28.0 and mathlib v4.28.0.

[Repository overview](../README.md) ·
[Code comparison and search](../site/lean/index.html)

The comparison page contains the exact Lean source, elaborated types,
mathematical paraphrases, references, and links to supporting definitions.
After downloading the repository, open `../site/lean/index.html` directly in
a browser. GitHub's file view displays HTML source; the local page supports
search and navigation without internet access or a Lean installation.

## Installation and verification

Install [elan and Lean](https://leanprover-community.github.io/get_started.html).
Open this directory in VS Code with the Lean 4 extension, or use a terminal.
Run these commands **from this `lean/` directory**:

```sh
lake exe cache get
lake build
lake env lean -j1 -M8192 Audit.lean
```

`lean-toolchain` selects Lean 4.28.0. `lake-manifest.json` pins mathlib at
`8f9d9cff6bd728b17a24e163c9402775d9e6a365` and its dependencies. Keep the
manifest and do not run `lake update` when reproducing this snapshot.
The first setup needs a network connection; offline builds require the
already downloaded toolchain, dependencies, and cache.

There are 3,171 mathematical Lean files. The first build may take time and
substantial disk space. The Lake configuration supplies `-j1 -M8192` to each
Lean process; this is a per-process setting rather than a total Lake memory cap.

`Audit.lean` checks every project declaration for transitive axiom dependencies.
It permits `propext`, `Classical.choice`, and `Quot.sound`, and rejects
`sorryAx`, native-decision axioms, and custom axioms. Literature propositions
are explicit theorem arguments; this audit does not prove those propositions.

## Where to start

| File | Contents |
| --- | --- |
| [Stage2IntrinsicClassification.lean](QuaternionicSymmetry/Stage2IntrinsicClassification.lean) | The four final metric and contact-line theorems. |
| [Stage2IntrinsicSources.lean](QuaternionicSymmetry/Stage2IntrinsicSources.lean) | The 15 retained literature inputs. |
| [Stage2IntrinsicGeometry.lean](QuaternionicSymmetry/Stage2IntrinsicGeometry.lean) | Actual geometric hypotheses, including the four-dimensional Einstein/Weyl convention. |
| [Stage2ContactInduction.lean](QuaternionicSymmetry/Stage2ContactInduction.lean) | Contact homogeneity by induction. |
| [ManifoldRiemannianIntrinsicSymmetry.lean](QuaternionicSymmetry/ManifoldRiemannianIntrinsicSymmetry.lean) | Global point symmetry of the given metric. |

`intrinsicSymmetric_c12` covers quaternionic dimensions 1–12 and assumes
`Sources` plus `DerdzinskiFourSymmetrySource`. `intrinsicSymmetric_e14` covers
1–14 with the additional `AmannInput`. The other two endpoints establish
generation and ampleness of the original twistor contact line for 2–12 or
2–14. The metric conclusion is intrinsic symmetry, not an explicit
isometry to a named Wolf model.

The active main proof uses a contact-section dimension bound and the Lie
algebra of the quaternionic-preserving isometry subgroup in the
Picard-generator branch. Separate full-isometry dimension theorems in
[ManifoldSWLieDimensionBound.lean](QuaternionicSymmetry/ManifoldSWLieDimensionBound.lean)
retain additional source hypotheses, including `KillingLieSource`.

## Regenerate the comparison data

From this directory:

```sh
lake env lean -j1 -M8192 tools/ExportBoundary.lean
cd ..
python3 tools/build_site.py
python3 tools/check_site.py
```

The export traverses declaration types, definition bodies, and structure
constructors, not theorem proof bodies. It describes the encoding of the
statements rather than the minimal premises used in their proofs.
[Site maintenance](../PUBLICATION.md) explains intentional snapshot updates.
