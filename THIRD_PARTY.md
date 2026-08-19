# Third-party source

Two Apache-2.0 Lean developments are vendored rather than depended on, so that
the exact proved statements are visible here and pinned by content rather than
by a floating branch.  The mathematical theorems they formalize are due to
their original authors, cited below; the Lean proofs are due to the vendored
projects' authors, named in the retained per-file notices and in `NOTICE`.

## Polynomial method for restricted sums

The files under
`LeanPool/PolynomialMethodRestrictedSums/` are derived from the
Apache-2.0-licensed project
`Vilin97/lean-pool`, directory
`LeanPool/PolynomialMethodRestrictedSums`, at commit
`3fc79f0a795f19fffcc59eee3efaf5faa52de3c3`.
The per-file copyright and author notices have been retained.

Local changes are limited to:

- Lean's module/public-import declarations required by this package;
- disabling both forms of automatic implicit-variable insertion;
- the Lean 4.33 compatibility rewrites `ite_eq_left/right` to
  `if_pos/if_neg` and `dite_eq_left` to `dif_pos`.

The project-facing theorem is
`Erdos289.RestrictedFold.image_card_lower_bound`.  Its statement is phrased
solely through the canonical fixed-cardinality subset object and its additive
fold; the polynomial coordinates remain internal.

The mathematical result is:

> Dias da Silva, J. A. and Hamidoune, Y. O., *Cyclic spaces for Grassmann
> derivatives and additive theory*.  Bulletin of the London Mathematical
> Society **26** (1994), no. 2, 140–146.  doi:10.1112/blms/26.2.140.

## Haxell's independent-transversal theorem

The files under `IndependentTransversals/` are derived from the
Apache-2.0-licensed project `Pjotr5/IndependentTransversals` at commit
`205372fe2b4b17ec77ef3f4629c43686223c1028`.  Only the four-module dependency
closure of `PartitionedGraph.haxell_theorem` is included.  Per-file copyright
and author notices have been retained.

Local changes are confined to Lean's module/public-import declarations,
disabling both forms of automatic implicit-variable insertion, and any
explicitly noted Lean 4.33 compatibility edits.

The mathematical result is:

> Haxell, P. E., *A note on vertex list colouring*.  Combinatorics, Probability
> and Computing **10** (2001), no. 4, 345–347.  doi:10.1017/S0963548301004758.

## Warnings from the vendored sources

The vendored modules still emit mathlib deprecation warnings (`Set.mem_diff`,
`Set.mem_setOf_eq`, `push_neg`, …).  They are left alone deliberately: the
local changes are kept to the minimum recorded above so that the diff against
upstream stays reviewable.  The modules this project authors are warning-free.
