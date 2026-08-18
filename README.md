# Erdős 289

A Lean 4 development of a universal graded affine-correction theorem and its
descent towards **Erdős problem 289**.

> Is it true that, for all sufficiently large $k$, there exist finite intervals
> $I_1,\ldots,I_k\subset\mathbb{N}$, distinct, not overlapping or adjacent, with
> $\lvert I_i\rvert\ge 2$ for $1\le i\le k$, such that
> $1=\sum_{i=1}^{k}\sum_{n\in I_i}\frac1n$?
>
> — [erdosproblems.com/289](https://www.erdosproblems.com/289)

Pinned to **Lean 4.33.0** and **mathlib v4.33.0**.

## The final theorem is not proved

This repository is explicit about its own state, and the state is:

* the universal core and five isolated hard leaves are **proved
  unconditionally** and transitively axiom-audited;
* the **unconditional Erdős 289 theorem is not claimed**.

`ROADMAP.md` says exactly which layers are missing and why. Read it before
taking any summary sentence here as a result about the conjecture.

## The statement, and why you can trust that it is the right one

The development states the problem intrinsically — a finite support in the
positive-integer path, its connected components, and the exact reciprocal
value:

```lean
def Erdos289Statement : Prop :=
  CofiniteSaturation 1 originalConstraint
```

An interval decomposition is a *presentation* of such a support, not an
invariant of it, so intervals do not appear in the intrinsic phrasing. That the
two phrasings agree is proved rather than asserted: `Erdos289/Literal.lean`
shows that a connected component of the induced path graph is convex, hence an
integer interval, and derives

| literal form | matches | theorem |
| --- | --- | --- |
| `Erdos289LiteralSeparated` | the sentence on erdosproblems.com/289 | `erdos289LiteralSeparated_of_statement` |
| `Erdos289Literal` | `erdos_289` in [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) | `erdos289Literal_of_statement` |

What is being developed is strictly stronger than the problem as posed: every
block has length two or three, and distinct blocks are required to be
non-adjacent.

## What is proved

* the universal graded affine-correction engine: realizer pullbacks, the
  compatible-composition epimorphism, literalization, and exact-spectrum
  transfer;
* canonical target centering, compact quotient resolution, and the least
  absorber universal property;
* the grade-resource quantale, free enriched closure, cyclic ladder, and the
  cofinal overlapping-interval theorem;
* the path-support partial commutative monoid, with reciprocal value and
  connected-component grade proved additive on every defined physical union;
* the constructive remote separated Egyptian leaf, every positive-rational
  presentation fibre derived from it, and arbitrarily light equal-grade
  mobility;
* the prime-power filtration of `ℚ/ℤ`, its simple fibres, and their additive
  equivalence with `ZMod p`;
* signed-inverse binary atoms, their factorization through the canonical
  prime-power stage, and their nonzero class in the associated simple fibre;
* the intrinsic quantitative transverse-reservoir interface, exposing only row
  size, simple-fibre multiplicity, atom mass and conflict degree;
* the five isolated hard leaves — see the table in `ROADMAP.md`.

## Verification

Three checks of different kinds, all run in CI. `lake build` succeeding does
not by itself mean the proof closure is assumption-free, so the axiom audit is
separate and its expected output is pinned with `#guard_msgs`.
`VERIFICATION.md` explains all three and how to reproduce them.

```bash
lake exe cache get
lake build            # includes Audit.lean, hence the transitive axiom audit
./scripts/source_scan.sh
```

Do not run `lake update`: the toolchain and every dependency revision are
pinned, and dependency bumps go through their own pull request.

## Layout

```text
AffineCorrection/     universal core (Part I); imports no E289 provider
Erdos289/             reciprocal descent (Part II)
IndependentTransversals/, LeanPool/
                      vendored Apache-2.0 providers; see THIRD_PARTY.md
Erdos289Test/         tests consuming only the deliberate public API
Audit.lean            transitive axiom audit
scripts/              hygiene checks run by CI
```

`DESIGN.md` records the binding three-layer rule: fix the intrinsic
mathematical object first, pass to an equivalent working language second, and
only then choose the Lean realization. A convenient witness may not replace a
universal object or a canonical fibre.

## Licence

Apache-2.0; see `LICENSE` and `NOTICE`. Two Apache-2.0 developments are
vendored rather than depended on, with their copyright notices retained;
`THIRD_PARTY.md` records the upstream commits and every local modification.
