# Named hypotheses

`Lamps.PermSweepBound` is the only unproved external mathematical premise used by this snapshot's
conditional headline theorems. Its definition is moved verbatim from `Lamps.CriterionSweep`.
It is the fixed-constant permutation consequence of the entropy step in the proof of
Theorem `thm:sweep` of Douglas–Mghirbi, *Amenable groups with nearly exponential sofic profile*,
v1.2.0, Section "Counting criteria", paragraph "Entropy from this error" and its constants.
The checked sweep theorem is conditional on this proposition. The hypothesis is not used by Theorem A.

The generic group notation and suffix maps are defined in `GroupTheory/`, so this module imports
no paper presentation. The QIT propositions remaining elsewhere have proofs and are mathematical
interfaces, not literature hypotheses. No assumptions from other packages are imported here.
