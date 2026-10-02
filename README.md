# Amenable groups with nearly exponential sofic profile, and quantum channels that need nearly linear memory

Seth Douglas and Nidhal Mghirbi — October 2026.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23050302.svg)](https://doi.org/10.5281/zenodo.23050302)

[Read the manuscript](paper.pdf) · [TeX source](paper.tex) ·
[Verification scope](verification/README.md)

How far from finite can an amenable group be? Every finite piece of an amenable group can be imitated by permutations
of a finite set, and Cornulier's sofic profile counts how many points such an imitation needs at accuracy 1/r. This
paper builds a finitely presented elementary amenable group with a finite piece whose profile is exp(r^(1+o(1))):
at least exp(c r/(log r)^12.75) and at most exp(C r log r), close to the most the underlying counting method can ever
detect. The lower bound is certified by 25 explicit relations in five generators.

The construction is a lamplighter with its lamps on configurations rather than on points. Houghton's group moves the
points of three rays, finitely supported affine maps act on their binary configurations, and a copy of S_3 sits on
every configuration. N points then carry 2^N lamps, yet any two lamps can be brought together by moves that each
involve at most three points. The group embeds in Brin's group 3V, so 3V has a finite piece whose profile is finite
and exp(r^(1+o(1))), whatever the answer to the open question of whether 3V is sofic.

The same relations define an explicit quantum channel on C^873, with Choi rank 130. Consider a device that applies it
n times, releasing each output before the next input arrives:
- If it may spend B bits of purity, it needs about n/B qubits of memory, and exact devices achieve this up to
  polylogarithmic factors.
- With logarithmic purity, it needs memory n^(1-o(1)).
- With exchange at the optimal rate, the least memory is n^(1/2+o(1)), attained with purity of the same order.

The channel is factorizable and lies in the closure of channels with finite maximally mixed baths, yet any such bath
that imitates it to accuracy u needs dimension exp(u^(-1+o(1))), although its minimal Stinespring dilation implements
it exactly with a pure environment of dimension 130. A local lattice process in nu dimensions whose bath starts
maximally mixed needs time about delta^(-1/nu) to produce the channel to accuracy delta.

This repository contains the preprint, its source, and finite verification scripts. The manuscript is the authority
for exact statements and hypotheses; the scripts do not constitute formal verification or peer review.

## License and citation

The manuscript and repository content are available under **CC BY 4.0**.
The software and machine-readable relation lists are additionally available under
the **MIT License**, at your option; see [RIGHTS.md](RIGHTS.md) for the scope.

Please cite Seth Douglas and Nidhal Mghirbi, *Amenable groups with nearly exponential sofic profile, and quantum
channels that need nearly linear memory* (2026), version 1.1.2,
[doi:10.5281/zenodo.23050302](https://doi.org/10.5281/zenodo.23050302) (all versions). [CITATION.cff](CITATION.cff) provides
machine-readable citation metadata. Tagged releases archive the corresponding manuscript and verification scripts
together.

The DOI above is the all-versions DOI, which identifies the evolving work. The v1.1.2 archive is
[doi:10.5281/zenodo.23111927](https://doi.org/10.5281/zenodo.23111927), the v1.1.1 archive is
[doi:10.5281/zenodo.23108312](https://doi.org/10.5281/zenodo.23108312), the v1.1.0 archive is
[doi:10.5281/zenodo.23107117](https://doi.org/10.5281/zenodo.23107117), the v1.0.2 archive is
[doi:10.5281/zenodo.23070871](https://doi.org/10.5281/zenodo.23070871), the v1.0.1 archive is
[doi:10.5281/zenodo.23065778](https://doi.org/10.5281/zenodo.23065778), and the v1.0.0 archive is
[doi:10.5281/zenodo.23050303](https://doi.org/10.5281/zenodo.23050303).

## Reproduce

Requires Python 3.10+ and a TeX distribution with the packages listed in paper.tex. No third-party Python package is
needed.

    python build.py
    python verification/run_all.py

The second command runs the five checks described in [verification/README.md](verification/README.md) and reports
each result.

Generated TeX build files stay in build/; paper.pdf is the canonical output. The bibliography is in
sections/references.tex. Each script prints its checks and exits with status 0 when all pass.

## Companions

This paper builds on two companion papers, each with its own repository:
- [Houghton's group H_3 has superpolynomial sofic profile](https://github.com/Apsiape/houghton-sofic-profile)
  (version 1.1.2, [doi:10.5281/zenodo.23070869](https://doi.org/10.5281/zenodo.23070869));
- [Causal quantum-channel simulation: memory beyond entropy](https://github.com/Apsiape/causal-quantum-memory)
  (version 1.1.2, [doi:10.5281/zenodo.23070870](https://doi.org/10.5281/zenodo.23070870)).

The proofs of the two results from them on which the main lower bounds stand, the counting criterion and sequential
extraction, are reproduced in Appendix B of the manuscript.
