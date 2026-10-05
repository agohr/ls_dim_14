# Exact verification of the finite identities

[Repository overview](../README.md) · [Lean development](../lean/README.md)

These scripts use Python's standard library and `fractions.Fraction`.
Python 3.10 or later is sufficient; there is nothing to install with pip.
The calculations run offline and do not require Lean. The printed-identity
checker reads two source files from the bundled `../lean/` directory as text.

## Run all checks

From the repository root:

```sh
python3 -B python/check_all.py
```

Or from this directory:

```sh
python3 -B check_all.py
```

All paths are resolved relative to the scripts, so either command can be run
from another working directory using its full path. A failed check exits with
a nonzero status. Do not use Python's `-O` or `-OO` options: the verifiers use
assertions and explicitly reject optimized execution.

## Individual checks

Commands below assume the repository root.

| Command | What it checks |
| --- | --- |
| `python3 -B python/verify_decompositions.py` | Reconstructs every density for n=2,…,14 and the current paper's rank-14 orbital decompositions: 12 profiles, seven support groups, 21 exact moment systems with normalized weights greater than 1/131072, and the mixed square at n=14. Also checks all six adjacent identities and character orthogonality through S6. |
| `python3 -B python/check_examples.py` | Checks the current paper's displayed profiles and support tables, D5 and D6 worked examples, moments of the (1,4) profile, quartic separator and mixed correction, and volume coefficients for n=5,…,14. Uses the decomposition verifier's arithmetic. |
| `python3 -B python/verify.py` | Reconstructs index densities for n=2,…,14; checks scalar reserves and maximum Weyl weights; printed positive certificates for n=5,…,12; orbital separator identities at n=13,14; PSD separator target values at n=11,12; and the complete H2 witnesses. |
| `python3 -B python/check_printed_identities.py` | Checks the transcribed density identities at n=5,…,12, projection/orbital conversions, Gaussian conversions, quartic separators, and the one-square certificates read from the Lean sources. Includes character orthogonality through S6 and two trace-normalization diagnostics. |
| `python3 -B python/adjacent_density.py` | Independently reconstructs the densities through n=14 and verifies the odd/even adjacent identities `2 D_(n−1) = D_n + u D_(n−2)` for even n=4,…,14. |
| `python3 -B python/verify_h2.py` | Checks the supplied n=13,14 rational orbital–square certificates, including every power of u: 29 positive orbital terms, one positive square, and 30 polynomial coordinates in each dimension. |

`orbital_polynomials.py` is a helper module. It constructs orbital
polynomials using the Murnaghan–Nakayama character rule and the Frobenius
formula. `verify.py` has an independent implementation of the density and
symmetric-function arithmetic.

The printed-identity checker reports **276 successful checks and two
normalization diagnostics**. The latter record the factor of 16 introduced
by using complex trace in place of the stated quaternionic trace in the
normalized quartic PSD moments. They are diagnostics, not failed equalities.
The counts include families grouped into individual checks; they do not
count every internal coefficient comparison.

## Optional reports

The default commands print their results without creating report files.
To save reports:

```sh
python3 -B python/verify.py --write
python3 -B python/check_printed_identities.py --output-dir python/results
```

The first command writes `python/results/exact_coefficients.json` and
`python/results/VERIFICATION.txt`. The second writes `exact_checks.json`
and `verified_one_square_certificates.json` in the selected directory.
Generated reports are excluded from the release archive and Git.

To check a different Lean checkout, supply its Lake project directory:

```sh
python3 -B python/check_printed_identities.py --lean-root /path/to/lean
```

## Data and scope

[data/decompositions_certificate.json](data/decompositions_certificate.json)
is the current paper's certificate, imported from Overleaf revision
`5e5c1d72532ffce1627b35f5b8c2a2935f2b5a26` on 5 October 2026.
`verify_decompositions.py` rebuilds the polynomials and solves the prescribed
moment systems exactly; it does not accept stored numerical approximations
as proof. `check_examples.py` checks transcribed worked formulas against
that verifier. Neither script needs the manuscript or creates output files.

[data/h2_witness_n13.json](data/h2_witness_n13.json) and
[data/h2_witness_n14.json](data/h2_witness_n14.json) contain the full rational
one-square witnesses. The printed-identity checker separately reads
`H2WitnessThirteen.lean` and `H2WitnessFourteen.lean` from the bundled Lean
snapshot and verifies their identities.

The formulas in `check_printed_identities.py` were transcribed for the
3 October 2026 manuscript review and supplement the current paper checks.
[data/provenance.json](data/provenance.json) records both manuscript
snapshot hashes and the origins of the scripts. These are explicit
coefficient checks, not an automatic comparison with a changing LaTeX file.
The n=13,14 witnesses are the one-square certificates used by the Lean
snapshot, not a reconstruction of the earlier manuscript's omitted
seven-square Gram matrix.

The scripts establish rational polynomial equalities and the stated
coefficient signs. They do not prove the analytic interpretation of Haar
moments, Hodge positivity, the remaining geometric inputs, or classification.
