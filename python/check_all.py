#!/usr/bin/env python3
"""Run all independent finite-identity checks, using only the standard library."""
from pathlib import Path
import subprocess
import sys


def main():
    if not __debug__:
        raise RuntimeError('Verification requires assertions; do not run Python with -O.')
    root = Path(__file__).resolve().parent
    # verify.py already includes verify_h2.py's complete witness checks.
    for name in ('verify_decompositions.py', 'check_examples.py', 'verify.py',
                 'check_printed_identities.py', 'adjacent_density.py'):
        print(f'\nRunning {name}', flush=True)
        subprocess.run([sys.executable, '-B', str(root / name)], check=True)
    print('\nPASS: all exact verification scripts completed.', flush=True)


if __name__ == '__main__':
    main()
