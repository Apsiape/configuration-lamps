# Amenable groups with nearly exponential sofic profile, and quantum channels that need nearly linear memory

Seth Douglas and Nidhal Mghirbi — November 2026, version 1.3.0.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23050302.svg)](https://doi.org/10.5281/zenodo.23050302)

[Read the manuscript](paper.pdf) · [TeX source](paper.tex) ·
[Verification scope](verification/README.md)

## Abstract

How far from finite can an amenable group be? Cornulier's sofic profile counts the points needed to imitate a fixed finite piece by permutations at a given accuracy. We build a finitely presented elementary amenable group with nearly exponential profile, close to the ceiling of our counting method. Its lamps are symmetric groups on three letters placed on binary configurations of three rays. The group embeds in Brin's group 3V, which therefore also has a finite piece of nearly exponential profile. A sweep form of the counting criterion charges a whole ordered suffix at once. Quadratic sweep fillings improve the lower bound for the dyadic lamplighter to exponential in the square root of the accuracy parameter, for the same finite piece.

The configuration group gives an explicit quantum channel in dimension 873 with Choi rank 130. A device that applies it repeatedly, releasing each output before the next input arrives, needs memory proportional to the number of uses divided by its purity budget, up to polylogarithmic factors; exact devices attain this tradeoff. At the optimal exchange rate the least memory is of square-root order, up to subpower factors, attained with purity of the same order. The channel is factorizable and is a limit of channels with finite maximally mixed baths, but accurate such baths require nearly exponential dimension in inverse error. A pure environment of dimension 130 implements it exactly. The engine is a one-round theorem: after one use, the device's memory carries an approximate representation of the group.

This repository contains the preprint, its source, finite verification scripts and a Lean 4 core of Part I. The Lean core proves Theorem 3.3(a)–(c) and the elementary-amenability part of (d) for the generated permutation group, Theorem 2.3 conditionally, and partial, existential or conditional forms of further Part I results, using only Lean's three standard axioms and passing the leanchecker and nanoda kernel checkers. Finite presentation, the wreath-product identification, Propositions 7.2–7.3 (3V embedding, Følner bound), the ladder, Parts II–III and the other results listed in lean/README.md are not formalized; [lean/README.md](lean/README.md) and Appendix J give the exact scope and the build commands. The finite scripts remain separate computational checks. The manuscript is the authority for its full statements; neither kind of checking constitutes peer review.

## License and citation

The manuscript and repository content are available under **CC BY 4.0**.
The software, Lean sources and machine-readable relation lists are additionally available under
the **MIT License**, at your option; see [RIGHTS.md](RIGHTS.md) for the scope.

Please cite Seth Douglas and Nidhal Mghirbi, *Amenable groups with nearly exponential sofic profile, and quantum
channels that need nearly linear memory* (2026), version 1.3.0,
[doi:10.5281/zenodo.23050302](https://doi.org/10.5281/zenodo.23050302) (all versions). [CITATION.cff](CITATION.cff) provides
machine-readable citation metadata. Tagged releases archive the corresponding manuscript and verification scripts
together.

The v1.2.0 archive is [doi:10.5281/zenodo.23875973](https://doi.org/10.5281/zenodo.23875973).
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

For the Lean core, see [lean/README.md](lean/README.md). The Python verification command runs the five checks described in [verification/README.md](verification/README.md) and reports
each result.

Generated TeX build files stay in build/; paper.pdf is the canonical output. The bibliography is in
sections/references.tex. Each script prints its checks and exits with status 0 when all pass.

## Companions

This paper builds on two companion papers, each with its own repository:
- [Houghton's group H_3 has superpolynomial sofic profile](https://github.com/Apsiape/houghton-sofic-profile)
  ([doi:10.5281/zenodo.23027624](https://doi.org/10.5281/zenodo.23027624), all versions);
- [Causal quantum-channel simulation: memory beyond entropy](https://github.com/Apsiape/causal-quantum-memory)
  ([doi:10.5281/zenodo.23027626](https://doi.org/10.5281/zenodo.23027626), all versions).

The proofs of the two results from them on which the main lower bounds stand, the counting criterion and sequential
extraction, are reproduced in Appendix B of the manuscript.
