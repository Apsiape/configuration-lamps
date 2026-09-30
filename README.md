# Amenable groups with nearly exponential sofic profile, and quantum channels that need nearly linear memory

Seth Douglas and Nidhal Mghirbi — September 2026.

[Read the manuscript](paper.pdf) · [TeX source](paper.tex) ·
[Verification scope](verification/README.md)

How far from finite can an amenable group be? This paper constructs a finitely presented elementary amenable
group whose finite pieces need nearly exponentially many points to be modelled by permutations. Its sofic profile is
exp(r^(1+o(1))): at least exp(c r/(log r)^12.75) and at most exp(C r log r). The lower bound is within a
polylogarithmic factor in the exponent of the most the underlying counting criterion can give. The group puts a
copy of S_3 on every finite binary configuration of the three rays of Houghton's group. N points carry 2^N copies,
yet any two copies are brought together by relations that touch only three points at a time. Its lower bound is
certified by 25 explicit relations in five generators. The group embeds in Brin's higher-dimensional Thompson group
3V, so 3V has a chunk whose profile is finite and exp(r^(1+o(1))), whatever the answer to the open question of
whether 3V is sofic.

The same relations define an explicit quantum channel on C^873. Consider a device that serves n uses of it,
releasing each output before the next input arrives:
- If it may spend purity B, it needs memory about n/B, and exact devices attain this up to polylogarithmic factors.
- With logarithmic purity, it needs memory n^(1-o(1)).
- At the optimal exchange rate, its memory is n^(1/2+o(1)) whatever its purity, and devices that keep one sofic model
  for all rounds attain this, with purity of the same order.

Consequently, a local lattice process in nu dimensions whose bath starts maximally mixed needs time about
delta^(-1/nu) to produce this channel to accuracy delta. Autonomous physics can still produce such channels: a bounded
time-independent Hamiltonian, not local, coupled to a bath in its tracial state, produces in the long run a channel
with the same memory-purity trade-off.

This repository contains the preprint, its source, and finite verification scripts. The manuscript is the authority
for exact statements and hypotheses; the scripts do not constitute formal verification or peer review.

## License and citation

The manuscript and repository content are available under **CC BY 4.0**.
The software and machine-readable relation lists are additionally available under
the **MIT License**, at your option; see [RIGHTS.md](RIGHTS.md) for the scope.

Please cite Seth Douglas and Nidhal Mghirbi, *Amenable groups with nearly exponential sofic profile, and quantum
channels that need nearly linear memory* (2026), version 1.0.0. [CITATION.cff](CITATION.cff) provides
machine-readable citation metadata. Tagged releases archive the corresponding manuscript and verification scripts
together.

## Reproduce

Requires Python 3.10+ and a TeX distribution with the packages listed in paper.tex. No third-party Python package is
needed.

    python build.py
    python verification/relators1d_check.py
    python verification/relators_check.py
    python verification/ladder_check.py
    python verification/embedding3v_check.py

Generated TeX build files stay in build/; paper.pdf is the canonical output. The bibliography is in
sections/references.tex. Each script prints its checks and exits with status 0 when all pass.

## Companions

This paper builds on two companion papers, each with its own repository:
- [Houghton's group H_3 has superpolynomial sofic profile](https://github.com/Apsiape/houghton-sofic-profile)
  (version 1.1, [doi:10.5281/zenodo.23048875](https://doi.org/10.5281/zenodo.23048875));
- [Causal quantum-channel simulation: memory beyond entropy](https://github.com/Apsiape/causal-quantum-memory)
  (version 1.1, [doi:10.5281/zenodo.23048998](https://doi.org/10.5281/zenodo.23048998)).
