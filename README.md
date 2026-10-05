# Supplementary Code and Data for the Paper "The LeBrun–Salamon conjecture is true in dimensions up to 56"

**Authors:** Aron Gohr, Marie-Amelie Lawn, Travis Schedler and Jordi Daura Serrano.

This repository contains exact Python checks of the finite identities and a
Lean development of conditional symmetry results for compact connected
positive quaternionic-Kähler manifolds.

## Contents

- [python/](python/README.md): exact rational verification scripts, coefficient
  data, and descriptions of the identities checked.
- [lean/](lean/README.md): the Lean development, pinned dependencies, and build
  instructions.
- [Lean code comparison and search](site/lean/index.html): a static browser for
  theorem statements, definitions, and their mathematical explanations.
  To use it offline, open `site/lean/index.html` in a browser after downloading
  the repository; GitHub's file view displays the HTML source.

## Run the Python checks

Python 3.10 or later is sufficient. No third-party packages or Lean
installation are required. From the repository root:

```sh
python3 -B python/check_all.py
```

The checks use exact rational arithmetic. See [python/README.md](python/README.md)
for individual commands, coverage, and the normalization conventions.

## Build the Lean development

Install [Lean and elan](https://leanprover-community.github.io/get_started.html),
then run:

```sh
cd lean
lake exe cache get
lake build
lake env lean -j1 -M8192 Audit.lean
```

The project pins Lean 4.28.0 and mathlib v4.28.0. Initial setup downloads the
pinned toolchain and dependencies; subsequent builds can run offline when
those files are cached. For editor support, open `lean/` in VS Code with the
Lean 4 extension. See [lean/README.md](lean/README.md).

## Mathematical scope

The Lean endpoints prove intrinsic symmetry of the given metric for
quaternionic dimensions 1–12, and through 14 with an additional Amann
intersection premise. They are implications from 15 explicit literature
inputs, with a separate four-dimensional input and the additional E14 input.
The conclusion is global metric point symmetry; an explicit catalogue of
Wolf spaces is not part of these endpoint statements.

The Python scripts verify polynomial identities and coefficient signs. They
do not establish the geometric interpretations or the literature inputs.
The exact statements and source comparisons can be read in the
[Lean explorer](site/lean/index.html).

## Offline browsing

Open `site/index.html` for a plain overview, or `site/lean/index.html` for the
code comparison and search. Both work directly from disk, without a server,
JavaScript packages, or external assets. Alternatively:

```sh
python3 -m http.server 8000 --directory site
```

Then visit <http://localhost:8000/>. Bibliographic links lead to external
publications; browsing the bundled code does not require a connection.

## Citing the Paper

If you use this code or data in your research, please cite the paper. The URL and publication details will be added when available.

```bibtex
@unpublished{GLSD26,
  author = {Gohr, Aron and Lawn, Marie-Amelie and Schedler, Travis and Daura Serrano, Jordi},
  title  = {The {LeBrun--Salamon} conjecture is true in dimensions up to 56},
  note   = {Manuscript},
  year   = {2026},
  url    = {PAPER_URL_TO_BE_ADDED},
}
```

## Reproducibility

The mathematical Lean sources are unchanged from development commit
`2ed2d163e0ea37930f1d478babaf38b4ad1b7520`; they now live under `lean/`.
The [source manifest](site-data/source-manifest.json) records paths relative
to that directory and their SHA-256 hashes. See [VALIDATION.md](VALIDATION.md)
for checks and [PUBLICATION.md](PUBLICATION.md) for site maintenance.

