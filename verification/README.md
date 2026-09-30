# Verification scope

The scripts in this folder are finite regressions for statements of the manuscript. They use the Python standard
library only, print each check, and exit with status 0 when every check passes. `run_all.py` runs all of them and
reports each result; `ladder_check.py` checks with assert statements and therefore refuses to run under python -O. They check the finite objects on
which the proofs rest; they do not check the general arguments, which are given in full in the manuscript.

## What is checked by machine

- `relators1d.txt`, `relators1d_check.py`: the 25 relations of the certificate of Theorem A (the table in the section
  "A certificate of 25 relations and local fillings"). The script rebuilds each word from its
  definition, confirms that it is freely reduced, and checks that it acts trivially in the faithful action of the
  group on pairs (configuration, element of S_3): the exponent sums, the action on every point and lamp site that the
  word can reach, and random configurations. As a negative control, deleting single letters from a sample of the
  relations gives words that act nontrivially.
- `relators.txt`, `relators_check.py`: the 77 relations of the grid variant (subsection "The grid host"), checked in
  the same style. The remark only sketches the profile bounds for the grid variant; the script checks the relations
  themselves, and proves that its box of test points is exhaustive.
- `ladder_check.py`: finite checks for the dyadic group and for the subgroup of Thompson's group V (section "Two steps up
  the ladder").
- `embedding3v_check.py`: the embedding of the configuration-lamp group in Brin's group 3V (subsection "An
  embedding in a Brin-Thompson group"). It represents elements of
  3V exactly as finite tables of prefix replacements, checks that the tables of the proof are partitions, checks the
  identities of the proof on random configurations, and checks that the images of the five generators satisfy the 25
  relations of the certificate while some non-relations and all single-letter deletions do not.

## What is not checked by machine

The pair-area theorem, the local fillings, the profile bounds, the hash models, the finite presentation, the
one-round theorem and all statements about quantum channels and physical dynamics are proved in the manuscript and
are not checked by these scripts.
