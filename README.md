# Erdős 289

A Lean 4 development of a universal graded affine-correction theorem and its
descent towards **Erdős problem 289**.

> Is it true that, for all sufficiently large $k$, there exist finite intervals
> $I_1,\ldots,I_k\subset\mathbb{N}$, distinct, not overlapping or adjacent, with
> $\lvert I_i\rvert\ge 2$ for $1\le i\le k$, such that
> $1=\sum_{i=1}^{k}\sum_{n\in I_i}\frac1n$?
>
> — Problem 289, [erdosproblems.com/289](https://www.erdosproblems.com/289)

Pinned to **Lean 4.33.0** and **mathlib v4.33.0**.

## The final theorem is not proved

This repository is explicit about its own state, and the state is:

* the universal core, the five isolated external inputs, the descent spine and
  the finite core stage are **proved unconditionally** and transitively
  axiom-audited;
* the **unconditional Erdős 289 theorem is not claimed**.

Exactly one obligation is open — the manuscript's *cofinal tail interface* —
and it appears as the single explicit hypothesis of

```lean
theorem smallBlockSaturation_of_tailInterface
    {D : ℕ} (hD : 0 < D) {s : ℚ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsupply : ∀ (F : Support) (τ : TargetResidue), ∃ N : ℕ, ∀ h, N ≤ h →
      ∃ (G : AddSubgroup TargetResidue) (ε : ℚ),
        τ ∈ G ∧ ε < s ∧
        TailCovers originalConstraint F
          (AddSubgroup.zmultiples (reciprocalResidue ⟨D, hD⟩)) G h ε) :
    SmallBlockSaturation
```

`ROADMAP.md` says exactly what is and is not proved, and why. Read it before
taking any summary sentence here as a result about the conjecture.

## Three statements, and how they are related

The development keeps the source-level sentence, the intrinsic problem class,
and the strengthening actually being proved separate, and proves the
implications between them.

| proposition | what it is | file |
| --- | --- | --- |
| `ErdosProblem289` | the sentence of problem 289, verbatim: eventually in `k`, `k` pairwise non-overlapping, non-adjacent intervals `[a_i, b_i]` with `0 < a_i < b_i` and `∑ᵢ ∑_{n ∈ [a_i,b_i]} 1/n = 1` | `Erdos289/Literal.lean` |
| `IntervalSaturation` | the same problem stated intrinsically: the exact reciprocal grade spectrum at `1` is cofinite, over the problem's own block-size class `{n \| 2 ≤ n}` | `Erdos289/Statement.lean` |
| `SmallBlockSaturation` | the strengthening this development proves: the same, with every block of length exactly two or three | `Erdos289/Statement.lean` |

```text
SmallBlockSaturation  →  IntervalSaturation  ↔  ErdosProblem289
  intervalSaturation_of_smallBlock    erdosProblem289_iff_intervalSaturation
```

An interval decomposition is a *presentation* of a finite support in the
positive-integer path, not an invariant of it, so intervals do not appear in
the intrinsic phrasing. That the two phrasings agree is an **equivalence
theorem**, not a claim: `Erdos289/Literal.lean` shows that a connected
component of the induced path graph is convex, hence an integer interval, and
conversely that an integer interval is connected, so a family of pairwise
non-adjacent intervals has exactly as many components as members.

`Erdos289Test/Smoke.lean` checks by `Iff.rfl` that `ErdosProblem289` is the
source sentence and not a paraphrase, and derives from it the weaker sentence
used by the `erdos_289` entry of
[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures),
which omits non-adjacency.

## Numerical constants

No numerical constant appears in a public statement unless it is part of the
source problem, part of an exact identity, or the sharp constant of a uniform
structural theorem. Everything else — the comparable band ratio, the
coefficient-fibre bound, the truncation rank, the core slack, the selector
target — is a parameter of the statement, and the particular value that the
present proof happens to use is a *witness* constructed inside a proof or
exhibited by a clearly labelled corollary.

For instance `Erdos289.ComparableBand` is existential in the band ratio `Λ`,
and `Erdos289.bandPrimes_card_isBigO` shows every integer ratio at least three
is one; `Erdos289.comparableBandThree` is the smallest witness the available
Chebyshev bounds supply. Replacing it by another valid ratio changes that one
definition and nothing downstream.

Numbers that *are* mathematics stay: the sharp four-point square-fibre bound,
the two-point bound at odd prime powers, the `2 · |obstacle|` deletion bound,
the selector interval `(0, 2)`, the block sizes `{2, 3}`. `DESIGN.md` lists
them with the mechanism each comes from.

An asymptotic statement is formalized as an asymptotic statement. It is never
replaced by an inequality valid beyond a hand-picked numerical threshold.

## What is proved

* the universal graded affine-correction theorem: realizer pullbacks, the
  compatible-composition epimorphism, literalization, and exact-spectrum
  transfer;
* canonical target centering, compact quotient resolution, and the least
  absorber universal property;
* the grade-resource quantale, free enriched closure, cyclic ladder, and the
  cofinal overlapping-interval theorem;
* the path-support partial commutative monoid, with reciprocal value and
  connected-component grade proved additive on every defined physical union;
* the constructive remote separated Egyptian presentation, every
  positive-rational presentation fibre derived from it, and arbitrarily light
  equal-grade mobility;
* the prime-power filtration of `ℚ/ℤ`, its simple fibres, and their additive
  equivalence with `ZMod p`;
* signed-inverse binary atoms, their factorization through the canonical
  prime-power stage, and their nonzero class in the associated simple fibre;
* the intrinsic quantitative transverse-reservoir interface, exposing only row
  size, simple-fibre multiplicity, atom mass and conflict degree, together with
  its bounded conflict degree and its packing into compatible pools;
* the row certificate of a prime-power current: the comparable carrier band,
  the uniform four-point square-fibre bound and its signed refinement, the
  carrier-deletion bound `4 (Λ - 1)`, deduplication by coefficient and rank
  truncation, all parametric;
* the composition law of the descent, stated as *compatibility*: a state
  avoiding a footprint together with its separation neighbourhood composes with
  anything inside that footprint, and only that is needed for admissibility,
  value, grade and residue to add;
* the descent spine — torsor induction, eventual trivialization of the residue
  filtration, and adjacent-lift uniqueness — which reduces the problem to two
  interfaces;
* at a prime current, the whole passage from a band of carriers to one link of
  the tail chain, including core-obstacle deletion and the asymptotic
  comparison of demand against the prime supply;
* both endpoints of the tail chain, through the identification of the
  `q`-torsion of `ℚ/ℤ` with the cyclic group generated by `1/q`;
* the **finite core stage**: a ladder of arbitrarily-light equal-grade switches
  realizing a complete cyclic torsor with any prescribed barrier slack;
* the five external inputs — see the table in `ROADMAP.md`.

## Verification

Three checks of different kinds, all run in CI. `lake build` succeeding does
not by itself mean the proof closure is assumption-free, so the axiom audit is
separate, its expected output is pinned with `#guard_msgs`, and its coverage is
derived from the sources rather than maintained by hand — every declaration of
`Erdos289/` and `AffineCorrection/` that is not `private` is audited.
`VERIFICATION.md` explains all three and how to reproduce them.

```bash
lake exe cache get
lake build            # includes Audit.lean, hence the transitive axiom audit
python3 scripts/source_scan.py
```

Do not run `lake update`: the toolchain and every dependency revision are
pinned, and dependency bumps go through their own pull request.

## Layout

```text
AffineCorrection/     universal core (Part I); imports nothing from Erdos289/
Erdos289/             reciprocal descent (Part II)
Erdos289.lean         publication root: re-exports the public mathematics only
IndependentTransversals/, LeanPool/
                      vendored Apache-2.0 sources; see THIRD_PARTY.md
Erdos289Test/         tests using only the deliberate public API
Audit.lean            transitive axiom audit
scripts/              hygiene checks run by CI
```

`DESIGN.md` records the binding three-layer rule: fix the intrinsic
mathematical object first, pass to an equivalent working language second, and
only then choose the Lean realization. A convenient witness may not replace a
universal object or a canonical fibre.

## References

The source of the problem statement, and the external theorems used.

* Bloom, T. F., *Erdős problems*, problem 289.
  <https://www.erdosproblems.com/289>. Accessed 2026-08. This page is the
  source of the sentence formalized as `Erdos289.ErdosProblem289`; it is also
  where the problem's provenance and its current status are recorded.
* Erdős, P. and Graham, R. L., *Old and new problems and results in
  combinatorial number theory*. Monographies de l'Enseignement Mathématique 28,
  Université de Genève, 1980. Background on the Egyptian-fraction problems of
  which this is one.
* Dias da Silva, J. A. and Hamidoune, Y. O., *Cyclic spaces for Grassmann
  derivatives and additive theory*. Bulletin of the London Mathematical Society
  **26** (1994), no. 2, 140–146. doi:10.1112/blms/26.2.140.
* Haxell, P. E., *A note on vertex list colouring*. Combinatorics, Probability
  and Computing **10** (2001), no. 4, 345–347. doi:10.1017/S0963548301004758.
* The mathlib Community, *The Lean mathematical library*. Proceedings of the
  9th ACM SIGPLAN International Conference on Certified Programs and Proofs
  (CPP 2020), 367–381. doi:10.1145/3372885.3373824. Chebyshev's bounds are used
  through `Mathlib.NumberTheory.Chebyshev`.

The Lean proofs of the Dias da Silva–Hamidoune and Haxell theorems are vendored
rather than reproved; `THIRD_PARTY.md` records their upstream commits, authors
and local modifications.

## Licence

Apache-2.0; see `LICENSE` and `NOTICE`. Two Apache-2.0 developments are
vendored rather than depended on, with their copyright notices retained;
`THIRD_PARTY.md` records the upstream commits and every local modification.

## Citing

See `CITATION.cff`.
