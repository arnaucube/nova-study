# nova-study [![Test](https://github.com/arnaucube/nova-study/workflows/Test/badge.svg)](https://github.com/arnaucube/nova-study/actions?query=workflow%3ATest)

Implementation of [Nova](https://eprint.iacr.org/2021/370.pdf) using [arkworks-rs](https://github.com/arkworks-rs/) just for learning purposes.

> Warning: Implementation from scratch to learn the internals of Nova. Do not use in production.

This repo is an ongoing implementation, the code will be dirty for a while and not optimized but just to understand and experiment with the internals of the scheme and try experimental combinations.

Thanks to [Levs57](https://twitter.com/levs57), [Nalin Bhardwaj](https://twitter.com/nibnalin) and [Carlos Pérez](https://twitter.com/cperezz19) for clarifications on the Nova paper.

### Details
_"Nova: Recursive Zero-Knowledge Arguments from Folding Schemes"_ (https://eprint.iacr.org/2021/370) by [Abhiram Kothapalli](https://twitter.com/abhiramko/), [Srinath Setty](https://twitter.com/srinathtv/), [Ioanna Tzialla](https://scholar.google.com/citations?user=IXTY4MYAAAAJ).

Current implementation uses a cycle of pairing-friendly curves with Groth16 for the compressed IVC proofs (as an example, the tests use MNT4, MNT6 curves), once the full scheme works, will see how many constraints the circuits need and might change one of the sides to a non-pairing curve with a non-pairing proof instead of Groth16. Eventually would like to explore also using BN254 with Grumpkin for ending up verifying the proofs in Ethereum.
