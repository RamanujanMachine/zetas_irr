MG55 zeta(3) proof package
6 October 2026

Main result: delta > 0.22521 and mu(zeta(3)) < 5.4402.
The sharper integer-only numerical certificate also gives delta > 0.22521567
and mu(zeta(3)) < 5.44019.

Read proof.tex for the complete argument and exact prime-profile table.

Verification (Python standard library only):
  python3 verify_arithmetic.py
  python3 verify_numerical_bounds.py

Independent symbolic verification (requires python-flint and sympy):
  python3 verify_matrix.py
  python3 verify_pairing.py

The arithmetic verifier recomputes all 270 floor chambers and endpoint
states, and proves c < 38.784 using integer and rational arithmetic.
The numerical verifier proves the spectral and final bounds using a
rational logarithm series with a rigorous remainder.
The matrix verifier reconstructs all 72 elementary steps independently;
it uses no RT installation, cached trajectory, or project input.
The pairing verifier checks the generic symbolic contiguity identities.

These are all-N algebraic/arithmetic certificates, not trajectory-depth
experiments. Numerical CMF checks were kept at depth 500 or below.
Additional derivations and exact finite audits are in the parent directory.
