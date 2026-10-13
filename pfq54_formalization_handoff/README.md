# Mathematical handoff: forward 5F4 and zeta(3), zeta(4)

Read `manuscript.tex` first. This is the reorganized mathematical exposition
for your formalizer. **There is no Lean implementation in this ZIP.**

The order is:

1. The conceptual integer-obstruction argument, independently of any CMF.
2. Coefficient normalization, harmonic denominators, and simultaneous common divisors.
3. The exact forward 5F4 start, direction, initial rows and projected ratio.
4. The supplied convergence construction, with the mode-transfer lemma made explicit.
5. The uniform arithmetic bound and nonvanishing argument.
6. The final comparison: error exponent 112.8 versus denominator exponent 112.5.

Detailed integral and prime-by-prime arguments are in the appendices, rather
than interrupting the conceptual explanation. Every reference within the
manuscript resolves; it compiled with the document editor's LaTeX compiler.
The open editor file was updated in place with the same manuscript.

## What the formalization must establish

`PROOF_STRUCTURE.md` lists the objects and exact lemma dependencies. The
arithmetic argument is for the actual harmonic numerator readouts, not a
substituted theta-derivative observable. The proposed uniform bound applies
to every fixed integer pair (A,B), including pairs whose target might be zero.

The supplied matrix script has passed its exact identities, initial-state
checks, invariant restriction, terminal projection and cyclicity checks.
An additional exact certificate gives

    vartheta = |rho4|/|rho1| < 1.02e-49 < exp(-112.8).

This spectral inequality is not itself a convergence theorem. The remaining
general analytic dependency is the modal-basis theorem for the rational
nonautonomous difference system. Its required statement is isolated in the
manuscript and in `PROOF_STRUCTURE.md`; the elementary dual-mode transfer is
proved explicitly. The integral decay proof, matrix transport, harmonic
readout bridge, common-divisor argument, and this asymptotic dependency all
need to be connected in the final formal proof.

Once these modules are justified, the argument yields

    liminf delta_n(A,B) >= 112.8/112.5 - 1 = 1/375 > 0.

This is a conditional consequence of the proposed proof, not a newly measured
numerical delta or an already formalized independence theorem.

## Included material

- `manuscript.tex`: standalone paper, with the conceptual argument first.
- `PROOF_STRUCTURE.md`: precise mathematical formalization plan; no Lean code.
- `source/convergence_original.tex`: your pasted lemma, preserved verbatim.
- `source/verify_5f4_meijerg_recessive.py`: your supplied verifier, unchanged.
- `source/verify_4f3_meijerg_coboundary.py`: your other supplied file, unchanged,
  included only as a reference example; it is not a premise of the 5F4 proof.
- `source/reproduce_spectral_data.py`: reconstruction of the exact limiting
  matrix, characteristic polynomial, cyclic determinant and rational root bound.
- `certificates/spectral_data.json`: those explicit exact objects.
- `certificates/supplied_5f4_check.log`: successful run of your supplied verifier.
- `supporting_checks/`: the existing arithmetic scripts and their required data.
- `MANIFEST.sha256`: checksums for the ZIP contents.

Optional reproduction, from the extracted ZIP root:

```sh
python -m pip install -r supporting_checks/requirements.txt
python source/verify_5f4_meijerg_recessive.py
python source/reproduce_spectral_data.py
cd supporting_checks
python work/pfq54_uniform_gcd/verify.py --finite
python work/pfq54_uniform_gcd/direct_binomial_readout.py
python work/pfq54_exact_writeup/verify_recurrence.py
```

Python checks provide finite certificates and implementation checks. They
are not a substitute for proving their universal mathematical interpretation.
No pickle payload or proof-assistant dependency is needed.

Scope report: the supplied convergence text, both supplied scripts, and the
existing arithmetic manuscript/certificates were inspected. This folder and
the final ZIP were created; the existing open manuscript was revised. The
5F4 identities were reproduced; no new candidate search or numerical delta
ranking was performed, and no unstable candidate was promoted. The next
verification target is the precise modal-basis statement for this restricted
system, together with the finite-sum/readout bridge; no wider search region
is recommended during this formalization handoff.
