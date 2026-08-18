# Third-party source

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

## Haxell's independent-transversal theorem

The files under `IndependentTransversals/` are derived from the
Apache-2.0-licensed project `Pjotr5/IndependentTransversals` at commit
`205372fe2b4b17ec77ef3f4629c43686223c1028`.  Only the four-module dependency
closure of `PartitionedGraph.haxell_theorem` is included.  Per-file copyright
and author notices have been retained.

Local changes are confined to Lean's module/public-import declarations,
disabling both forms of automatic implicit-variable insertion, and any
explicitly noted Lean 4.33 compatibility edits.
