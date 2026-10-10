CMF proof: 1, zeta(3), zeta(4) are linearly independent over Q
6 October 2026

Read proof.tex. Parts I-VI contain the simultaneous argument, including the
new second-derivative residue identity and the integer-matrix nonvanishing
argument. Part VII reproduces the full underlying spectral/arithmetic proof.

Standard-library exact arithmetic certificate:
  python3 verify_arithmetic.py arithmetic_certificate.json

The certificate proves the simultaneous denominator cost <57.784, strictly
below the linear-form decay rate >59.51995592483.

Other self-contained certificates:
  python3 verify_numerical_bounds.py
  python3 verify_matrix.py independent_matrix_certificate.json
  python3 verify_pairing.py pairing_certificate.json
The last two require python-flint/SymPy and SymPy respectively. The numerical
script concerns the shared spectral constants and underlying zeta3 bound.

No Lean formalization has been performed. The proof explicitly lists the
formalization obligations. Finite-depth checks supplement, but do not replace,
the all-N transport and integrality arguments.

Finite exact coefficient audit of the new second-functional identity:
  python3 verify_second_functional.py
This requires python-flint and SymPy and reads the independently generated
matrix certificate in this directory. It checks all three columns; the
all-N proof is the transport lemma in the document.

Exact audit of every second-functional axis step and boundary condition:
  python3 verify_transport.py
It checks 72 steps at N=1 and 144 steps at N=2, using the independently
constructed matrix certificate and no RT installation.
