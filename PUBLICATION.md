# Site and repository maintenance

The repository landing page is `README.md`. The optional GitHub Pages entry
at `site/index.html` is a plain academic overview with installation commands.
The code comparison and search lives at `site/lean/index.html`; its source
viewer is `site/lean/source.html`. The old promotional, build, and separate
literature pages have been removed.

## Local preview

No build step is required to browse the checked-in pages. Open
`site/index.html` or `site/lean/index.html` directly in a browser, or run:

```sh
python3 -m http.server 8000 --directory site
```

Visit <http://localhost:8000/>. All browser assets and declaration data are
local. Bibliographic links open external publications.

## Generate and check

From the repository root:

```sh
python3 -B python/check_all.py
python3 tools/build_site.py
python3 tools/check_site.py
```

The site tools need only Python 3.10+. The generator also writes a deterministic
`site/downloads/ls_dim14-source.zip` and `SHA256SUMS`. The ZIP includes both
`python/` and `lean/`, their instructions, the coefficient data, and the offline
explorer. It excludes build caches, Python results, repository history,
symlinks, and literature PDFs.

`python3 tools/build_site.py --check --no-archive` checks that the committed
pages and browser data match the maintained inputs. `tools/check_site.py`
also checks the full archive and therefore requires the ordinary build first.

## Maintained files

- `README.md`, `python/README.md`, `lean/README.md`: installation and scope.
- `tools/templates/index.html`: the plain Pages overview; keep its commands
  and scope consistent with the repository README.
- `tools/templates/lean/`: the comparison and source-viewer pages.
- `site/assets/style.css`, `site/lean/assets/explorer.js`: local presentation
  and browser behavior.
- `site-data/catalogue.json`: mathematical paraphrases, correspondence notes,
  bibliography, and the optional `config.repository_url`.
- `lean/tools/ExportBoundary.lean`: the statement-encoding graph exporter.

Do not edit generated HTML, `site/lean/assets/data.js`, or `site/lean/data/`
by hand. Run the generator after changing their maintained inputs.

## Updating the Lean snapshot

The source manifest's paths remain relative to the Lake project, now `lean/`.
Moving the project did not change any mathematical source or its hash.
To intentionally update the mathematics:

1. Build and audit from `lean/`: `lake build`, then
   `lake env lean -j1 -M8192 Audit.lean`.
2. Run `lake env lean -j1 -M8192 tools/ExportBoundary.lean` from `lean/`.
   Its default output is `../site-data/kernel.json`.
3. Review the source record and catalogue together. If the 15-field input
   inventory changes, update the catalogue, inventory checks, and descriptions.
4. Update the development commit and SHA-256 inventory in
   `site-data/source-manifest.json` deliberately, preserving paths relative to
   `lean/`. This records a verified new snapshot rather than bypassing checks.
5. Regenerate the site, run its checks, and review the comparison panels.

To compare a fresh export without changing the committed file, from `lean/`:

```sh
BOUNDARY_OUTPUT=/tmp/ls_dim14-kernel.json lake env lean -j1 -M8192 tools/ExportBoundary.lean
cmp ../site-data/kernel.json /tmp/ls_dim14-kernel.json
```

The graph follows project declaration types, definition bodies, and structure
constructors. It does not follow theorem proof bodies. Compiler helpers are
retained and can be displayed. Mathematical explanations are editorial;
the generator does not certify their fidelity to the literature.

## GitHub Pages

The prepared workflow uses `lean/` as the Lake package directory, checks the
Python identities, builds and audits Lean, compares the exported graph, and
checks the site and archive. Its directory setting is documented by
[lean-action](https://github.com/leanprover/lean-action#configuration).
The uploaded Pages artifact is the `site/` directory. Repository-root files
and Lean build caches are not deployed as web assets.

The repository URL is set in `config.repository_url` in
`site-data/catalogue.json`. Regenerate the site after changing it; a blank
URL is also valid for local use.

Pushes to `main` and pull requests run verification. Pages artifact upload
and deployment are opt-in: both require the repository Actions variable
`ENABLE_GITHUB_PAGES` to be exactly `true`. To enable hosting deliberately,
select GitHub Actions in the repository's Pages settings and set that
variable. Deployment then runs only for `main`, outside pull requests.
Offline browsing needs neither Pages nor that variable.

The root MIT license covers this repository; dependencies and cited works
retain their own licenses.
