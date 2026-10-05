# Local validation

Rechecked on 5 October 2026 after separating the repository into `python/`
and `lean/` and reducing the website to a plain overview and the Lean explorer.
Mathematical source revision: `2ed2d163e0ea37930f1d478babaf38b4ad1b7520`.

## Lean

- All 3,171 mathematical Lean files still match the recorded SHA-256 inventory
  byte for byte. Manifest paths are relative to the new `lean/` directory.
- `lake build`, run from the relocated Lake project, completed successfully:
  **7,446 jobs**. It reused the matching development cache; this was not a
  clean-room recompilation or a fresh dependency download.
- A fresh `lake env lean -j1 -M8192 Audit.lean` audited **27,051 declarations**,
  allowing only `propext`, `Classical.choice`, and `Quot.sound`.
- A fresh `tools/ExportBoundary.lean` run from `lean/` exported **15 source
  fields, 22 roots, and 1,502 declarations**. The output matched the saved
  `site-data/kernel.json` byte for byte.
- The protected build/export/audit run peaked at **1.50 GiB**, with no
  out-of-memory event. The temporary cache symlink was removed afterward.

## Python

- The current paper's decomposition verifier, worked-example checker, and
  certificate were imported from Overleaf revision `5e5c1d7`. Only data paths
  and rejection of optimized Python execution were adapted. They verify all
  21 exact moment systems and the complete polynomial reconstructions.
- `python3 -B python/check_all.py` passed. This covers the complete rational
  certificates, cone separators, scalar reserves, witness signs and powers,
  character orthogonality, and adjacent-dimension identities.
- The printed-identity checker completed **276 successful checks plus two
  trace-normalization diagnostics**. Both n=13,14 Lean certificates have
  29 positive orbital terms and one square.
- The generated archive was extracted outside the workspace. All checks ran
  successfully from an unrelated working directory using only its bundled
  Python scripts, coefficient files, and Lean sources read as text.
- The standalone `verify_h2.py` command and both optional report-writing
  commands passed in the extracted archive. No third-party Python packages
  or Lean installation were needed by the Python verification scripts.

## Offline pages and packaging

- `tools/check_site.py` verifies the graph and catalogue, exact source
  excerpts, local HTML links, all archived mathematical source hashes, the
  Python and Lean directory layout, and deterministic site/archive generation.
- The site has only three HTML pages: `index.html`, `lean/index.html`, and
  `lean/source.html`. The source archive includes both development folders,
  their documentation, data, and the offline explorer. Generated Python
  reports and Lean/dependency caches are excluded.
- Chrome checks passed at desktop (1440 px) and mobile (390 px) widths on the
  extracted archive, both over a local HTTP project subpath and directly via
  `file://`. HTTP and HTTPS requests were blocked during the file checks.
- Browser checks covered keyboard expansion, side-by-side comparisons,
  search and empty results, relevance filters, definition links, pagination,
  compiler helpers, theorem deep links, source paths and line anchors, and
  copy controls. There were no JavaScript exceptions.
- The landing page has no JavaScript dependency. All 17 literature
  comparisons remain readable with JavaScript disabled. Desktop and mobile
  screenshots were visually reviewed.

The GitHub workflow was updated for `lean/` and the Python checks, but has
not been run on GitHub. The site has not been deployed. A fresh Lean setup
still needs the pinned toolchain and dependency downloads before offline use.

The Lean checks verify the conditional proofs and source integrity. The
Python checks verify the finite identities described in their README.
Neither certifies the editorial paraphrases or the remaining literature
contracts.
