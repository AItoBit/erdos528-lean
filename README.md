# Erdős 528: known limit-existence theorem

**This does not solve Erdős 528.** The problem asks to determine the connective
constants. This project formalizes the known theorem that the limit exists,
using a finite signed-direction encoding, submultiplicativity, and Fekete's lemma.
The complete limit-existence proof passed [kernel verification and axiom
checks](https://github.com/AItoBit/erdos528-lean/actions/runs/38033406343).
Its main declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
An independent AI audit checked the statement, prefix/suffix injection, positivity,
and logarithmic limit argument.

Sources:
- [Erdős 528](https://www.erdosproblems.com/528)
- Hammersley and Morton, *Poor man's Monte Carlo*, J. Roy. Statist. Soc. Ser. B
  (1954), 23–38; discussion 61–75.
- [Grimmett–Li, §1.1](https://arxiv.org/html/1704.05884v2), which records the
  submultiplicativity argument and explains that the square-grid value is unknown.

Lean and Mathlib: 4.33.1. Run `lake exe cache get`, `lake --wfail build Erdos528`,
then `lake env lean PrintAxioms.lean`. CI checks that the final declarations use
only `propext`, `Classical.choice`, and `Quot.sound`.

Developed with AI assistance using the Erdős Research Lab plugin. No claim of a
new mathematical result is made.
