CMF proof certificate handoff -- 6 October 2026

The archive contains two matching source/certificate packages:

zeta3/  Original zeta(3) proof, delta > 0.22521 and mu < 5.4402.
        Its arithmetic verifier certifies denominator cost < 38.784.
zeta34/ Later simultaneous zeta(3), zeta(4) proof.
        Its arithmetic verifier certifies denominator cost < 57.784.

Each directory contains proof.tex, verify_matrix.py, verify_arithmetic.py,
the other verification scripts, and recorded JSON outputs. Match the
directory to the PDF being audited. The identically named arithmetic
scripts concern different bounds and must not be interchanged.

No RT installation or original author's local paths are needed.

RUN IN A WRITABLE COPY

Create a Python environment at the archive root (Python 3.8 or newer;
a recent Python is recommended for dependency availability):

  python3 -m venv .venv
  . .venv/bin/activate
  python -m pip install python-flint sympy
  export PYTHONOPTIMIZE=0

In either zeta3/ or zeta34/, run:

  python verify_arithmetic.py arithmetic_certificate.json
  python verify_numerical_bounds.py numerical_certificate.json
  python verify_matrix.py independent_matrix_certificate.json
  python verify_pairing.py pairing_certificate.json

In zeta34/ also run, after the matrix script:

  python verify_second_functional.py
  python verify_transport.py

Important details:
- Keep Python assertions enabled: do not pass -O or -OO.
- These scripts recompute checks. Positional JSON paths, where accepted,
  are OUTPUT paths, not input certificates being verified. The original
  zeta3 arithmetic script prints its result rather than writing that path.
- The last two zeta34 scripts read independent_matrix_certificate.json
  beside the scripts and overwrite their respective audit JSON outputs.
- The arithmetic and numerical scripts use only the standard library.
  The pairing script needs SymPy. The matrix, second-functional, and
  transport scripts need both python-flint and SymPy.
- The zeta34 numerical script concerns shared spectral constants and
  the underlying pure-zeta(3) bound; use its arithmetic script for the
  simultaneous denominator bound.

SCOPE

The written proof supplies the all-N arguments. Exact symbolic and
arithmetic computations support the specified proof steps. The finite
transport and endpoint checks do not independently prove an all-N
identity. No Lean formalization has been completed. The JSON outputs
are records to reproduce, not substitutes for checking the scripts
and the mathematical arguments connecting them to the theorem.

LOCAL SOURCE LOCATIONS

Relative to the CFM PAPER project directory:
  results/zeta3_proof_20261006/proof_package/
  results/zeta34_proof_20261006/

These are local task artifacts. Their presence here does not establish
that they are committed or available in a separate auditor checkout.
