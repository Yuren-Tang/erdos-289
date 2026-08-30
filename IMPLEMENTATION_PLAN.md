# E289 Lean 4.33.0 implementation plan

This document is an engineering execution plan. It does not amend, interpret,
weaken, or supplement the sealed mathematical specification. The canonical
input is the archive with SHA-256
`76b2ddd0797cea4d8614f1528c4a7f070c912d0a12418b5de9bd867a29142517`.
Any conflict is resolved in favour of that sealed input.

## 1. Fixed constraints

- Lean and Mathlib are both fixed at `v4.33.0`.
- Mathematical statements, binder order, filters, witnesses, constants, and
  proof routes are translated from the specification; they are not redesigned.
- The private construction certificates are transcribed verbatim. No finite
  search, numerical replacement theorem, or concrete-structure substitute is
  permitted.
- The 50-module direct-import graph is exactly `MODULE_IMPORTS.toml`.
- Public API ownership and gate placement are exactly
  `PUBLIC_INTERFACE_SPEC.toml`; theorem-facing objects are exactly
  `MATHEMATICAL_OBJECT_SPEC.toml`; dependent signatures are exactly
  `09_BINDER_LEVEL_SIGNATURES.md`.
- Remote CI remains absent during implementation. All ordinary validation is
  local. A final remote check may be added only after the complete local audit
  and only as a separately reviewable final action.

## 2. Baseline audit

The sealed package has been checked before implementation:

- archive digest matches the identifier above;
- all 13 manifest-listed payload hashes and byte sizes match;
- 50 module contracts match the 50 machine-readable module names;
- every project import resolves, the graph is acyclic, and it has 20
  topological levels;
- 57 public interface IDs are unique and owned by declared modules;
- 122 mathematical-object IDs are unique and all referenced API IDs resolve;
- the gate distribution is U 21, R0 5, L 12, R 6, B 4, T 2, E 3, D 4.

These counts are audit invariants, not implementation targets to be adjusted.

## 3. Validation model

Each node below has the same entry, implementation, and exit discipline.

### Entry

1. Every direct predecessor builds locally.
2. The module contract, owned public interfaces, object definitions, binder
   signatures, proof-obligation entries, and applicable private certificate
   have been cross-read.
3. Before coding, make an ownership matrix whose rows are the module's owned
   API IDs, mathematical objects, characterization obligations, and public
   theorem names. Record the expected direct imports beside it.
4. If a proof needs scaffolding owned by a different module, first expose the
   invariant/core theorem from its frozen owner; keep representation-specific
   wrappers in the consuming module.

### Implementation

1. Create only the declarations owned by the module.
2. Translate definitions first, then their fixed characterizations, then the
   fixed proof route.
3. Prefer existing Mathlib abstractions and lemmas. Local bridge lemmas are
   allowed only when they preserve the specified statement and route.
4. Compile the module after each coherent declaration group.
5. Add a consumer smoke check where a dependent binder or coercion is not
   visible from the producer alone.
6. Keep parenthesizations, concrete pullback bookkeeping, and other chosen
   representations out of downstream APIs unless the frozen owner contract
   explicitly exports them.

### Exit

1. The module and every affected public root build locally with Lean 4.33.0.
2. Its direct project imports equal the normative list; no transitive import is
   used as an undeclared dependency.
3. Public declarations match the sealed binder order and dependent objects.
4. No `sorry`, `admit`, project `axiom`, placeholder, numerical surrogate, or
   alternate mathematical statement remains.
5. `#print axioms` audit entries contain only the intended foundational
   principles already present in Lean/Mathlib.
6. Source scans and the relevant consumer smoke checks pass.
7. The owner-module audit checks every row of the entry ownership matrix; a
   theorem checked only from a consumer module does not discharge ownership.

A node is committed and uploaded only after its exit criteria pass. A failed
node remains local and is repaired before any dependent node starts.

## 4. Work order and checkpoints

The order respects both the exact import DAG and the mathematical gates. Modules
inside a node may be developed in the displayed order unless their direct-import
edges force a stricter order.

### M0 — reproducible local baseline

- Pin `lean-toolchain` and `lakefile.toml` to 4.33.0.
- Commit `lake-manifest.json` with the resolved Mathlib revision.
- Build the two empty public roots locally.
- Record the sealed-spec digest and this execution plan.

Checkpoint: `M0-local-baseline`.

### U0 — independent universal primitives

- `Universal.ReflexiveGraph`
- `Universal.Asymptotics`
- `Universal.AffineFiber`
- `Universal.Target.Centering`

Focus: categorical connected components, ENNReal-native uniform asymptotics,
affine-fibre extension, and marked-family centering.

Checkpoint: `U0-primitives`.

### U1 — finite components and physical carrier

- `Universal.FiniteComponentState`
- `Universal.ComponentProfileQuotient`
- `Universal.NaryCompatibility`
- `Universal.PhysicalPartialMonoid`

Focus: universal component profile, arbitrary killed-type quotient, direct
n-ary compatibility, and the physical partial monoid.

Checkpoint: `U1-physical-spine`.

### U2 — correction spine

- `Universal.Correction.Observation`
- `Universal.Correction.Core`
- `Universal.Correction.Realizer`
- `Universal.Correction.Composition`
- `Universal.Correction.Translation`

Focus: coherent observations, correction objects, realizers/covers, n-ary
composition, and the abelian translation certificate.

The abelian specialization is represented by an
`AddCommGrpCat`-valued observation functor and then forgotten to the existing
`AddCommMonCat` interface.  The grading object `M` remains an arbitrary
commutative additive monoid.  The frozen translation subtracts only in the
`Q(i)` coordinate; its grade coordinates come from the two correction labels,
and the composite-required grade equality closes their final sum.

Checkpoint: `U2-correction-spine`.

### U3 — targets and profiles; Gate U

- `Universal.Target.CompactResolution`
- `Universal.Target.LeastAbsorber`
- `Universal.Target.ExactTransfer`
- `Universal.Profile.GradeResource`
- `Universal.Profile.BoundSaturation`
- `Universal.Profile.FreeClosure`

Run the full 21-interface Gate U audit and consumer checks.

At Gate U, audit the regular-epimorphism boundary explicitly.  The correction
spine's current `Covers` interface is the surjectivity characterization in
the frozen `Type` setting.  If Translation, ExactTransfer, or any later
consumer uses a general categorical regular-epi API, first export an explicit
`Type` bridge (surjective implies split epi, hence regular epi); never treat
surjectivity as regular epimorphicity in an arbitrary category.

The bridge is now exported as `TypeRegularEpi`, using canonical universe lifts
to place source and target in one `Type` category, together with the proved
equivalence `type_regularEpi_iff_surjective`.  Owner-side invariant forms are
exported for `Covers`, the n-ary composition criterion, and the target-realizer
pullback.  The same closure pass completed the full least-absorber short exact
sequence, naturality of the component-profile Hom equivalence, and the U6.3
quotient/requirement/target-realizer comparison maps with U4.3 coherence.

The profile closure now uses the literal powerset quantale, its arbitrary-join
free universal property, and the grade-fixed upper-closure operator.  Its
fixed points are equipped with the reflected Minkowski tensor and audited as
a complete additive quantale.  `PhysWitness` retains the finite family,
zero-correction cover, and branchwise resource bound; `Phys` is its proved
fixed point.  The U7.7 certificate consumes the unreflected finite path-label
locus, and the public transfer theorem derives saturation only through the
reflection and resource-upper-closure laws.

Checkpoint: `gate-U`.

### R0 — reciprocal specialization

- `Reciprocal.State`
- `Reciprocal.CenteredResidue`
- `Reciprocal.CompactSubgroups`
- `Reciprocal.CurrentFiltration`
- `Reciprocal.Filters`

Focus: exact state/grade/value definitions, centered residue, compact subgroup
arithmetic, currents/predecessors/heights/endpoints, and named filters.

The successor graph is the reflexive symmetric graph on `ℕ_{>0}` whose relation
is `|m-n| ≤ 1`, so its graph distance is the one used by the finite physical
constraints.  Connected components of a state are proved to be order-convex,
which is the component/interval fact consumed by the later envelope map.  The
reciprocal value is the vertex fold of `n ↦ 1/n`, and `W₊` is its unique
nonnegative corestriction.

`A = ℚ/ℤ` is defined as `ℚ ⧸ zmultiples 1` and identified with the centered
target of the one-point marking at `τ = 1`.  The compact-subgroup lattice
`KSub(A)` is realized as the compact elements of the subgroup lattice of `A`;
every compact subgroup is the unique `H_n` of its own cardinality, and the
order, joins, and meets are divisibility, `lcm`, and `gcd`.  Currents are the
nonzero join-irreducible compact stages.  Their prime-power description, the
lower-current stage, the simple factor, the intrinsic height, the predecessor
map, and the canonical endpoints are all derived from those intrinsic
definitions; the arithmetic coordinates appear only as proved equivalences.
The simple factor carries the canonical `ZMod p_J`-scalar structure supplied by
its own `p_J`-torsion additive-group structure, and R2.3 one-dimensionality is
stated at the linear level as an inhabited `ZMod p_J`-linear equivalence; no
basis is chosen and the scalar action is not transported across any additive
equivalence.
The named filters are the rank pullback of `atTop`, its height-one
restriction, the endpoint index filter and its image, and the canonical
current tail, whose restriction is proved equivalent to the ambient current
filter.

Checkpoint: `gate-R0`.

### L0 — independent leaf foundations

- Neutral: `Neutral.Fibres`, `Neutral.Cube`
- Prime growth: `PrimeGrowth.Chebyshev`, `PrimeGrowth.ComparableBands`
- Restricted fold: `RestrictedFold.Basic`, `RestrictedFold.Polynomial`,
  `RestrictedFold.ImageGrowth`
- Packing local branch: `Packing.RowedGraph`, `Packing.Sharpness`

The fixed certificates CERT-N, CERT-PI, and CERT-RF are translated here.

Realized as follows.

`Neutral.Fibres` carries the run-family machinery: a family of pairwise
separated consecutive successor runs, the identification of its connected
components with its runs and of its component cardinalities with its run
lengths, and hence the E289 state it induces, together with that state's
reciprocal value, component profile, grade, constraint admissibility,
remoteness from a finite forbidden support and linear lightness bound.  On top
of this sit the group completion `Gr(M)` of the component-profile monoid with
its generators `e₂` and `e₃`, the neutral pair object with its profile
difference `Δχ`, the two fibres `Neu_g` and `Neu_δ`, the two sealed identities
of CERT-N A.1 and A.2 at `a = 2l+4`, and `neutralFibres_remote_light`.

`Neutral.Cube` adds the criterion that a family of states with pairwise
separated supports factors through the direct n-ary physical compatibility
locus, the neutral-type object `{e₂, e₃-e₂}`, the neutral coordinate object
with its four sealed clauses, the finite neutral cube with its selectorwise
compatibility field, and `neutralCube_regularEpi`, obtained by iteratively
strengthening the finite constraint by the complete two-alternative footprints
of the earlier coordinates.

`PrimeGrowth.Chebyshev` reads the sealed prime-log functions off Mathlib's
Chebyshev `θ` and `ψ`, records the four growth bounds, shows the Chebyshev
error term sublinear, and packages the two-sided linear band as
`PrimeLogBounds`.  `PrimeGrowth.ComparableBands` adds the admissible-dilation
subtype with its inhabitance, the prime band `(X, ΛX]`, and its two-sided
cardinality law.

`Packing.RowedGraph` carries the finite rowed graph, its row fibres, its
independent subobjects and its independent transversals.  `Packing.Sharpness`
adds the disjoint sum of simple graphs, the amalgam of two rowed graphs along a
dissolved row, obligation P.6, the complete bipartite obstruction `K_{d,d}`,
and obligation P.7: for every `d ≥ 1` a finite rowed graph of maximum degree
exactly `d` with `2d` rows, each of cardinality `2d-1`, and no independent
transversal.

`RestrictedFold.Basic` carries `FinSub`, the additive fold and its image,
together with their equivariance under additive and linear isomorphisms.
`RestrictedFold.Polynomial` carries the finite-grid coefficient detector
(RF.1), the universal alternation and the falling-factorial determinant (RF.2),
the coefficient formula for `(x_1 + ⋯ + x_h)^m Vdm(x)` in division-free and
divided form (RF.3), and the fixed-sum exponent constructor (RF.4).
`RestrictedFold.ImageGrowth` carries the top-degree comparison for a product of
affine factors, the base-changed alternation, the image-growth theorem over
`F_p` (RF.5) and its basis-free descent along the frame torsor of a
one-dimensional `F_p`-vector object (RF.6).

Checkpoint: `L0-independent-leaves`.

### L1 — Haxell preflight and packing; Gate L

Before importing Haxell:

1. Fetch `Pjotr5/IndependentTransversals` at commit
   `205372fe2b4b17ec77ef3f4629c43686223c1028`.
2. Verify the four sealed source blob digests from the provenance ledger.
3. Build those sources in an isolated Lean/Mathlib 4.33.0 preflight.
4. Permit only import, syntax, namespace, and API compatibility edits. Record
   every compatibility diff and the resulting digests; do not change theorem
   statements or proof ideas.
5. Implement `Packing.Haxell` and then `Packing.QuotaTransversal`.

Run the full 12-interface Gate L audit.

Checkpoint: `gate-L`.

### R — transverse rows

- `Transverse.Atom`
- `Transverse.RawRows`
- `Transverse.SparseSurvival`
- `Transverse.RowTransparency`

CERT-E fixes the signed inverse rows. The simultaneous raw-row object and its
tail filter are implemented before any consumer. Uniform sparse survival uses
the specified `ENNRealLittleO`/`UniformLittleO` route, not a normed-space
substitute.

Checkpoint: `gate-R`.

### B0 — prefix provider

- `Prefix.Provider`

Translate CERT-H in its fixed order: arithmetic endpoint, bridge rows, exact
root lists, repeated affine-fibre accumulation, grade equalization, mass
margin, uniform window incidence, predecessor escape, and transparency.

Checkpoint: `B0-prefix`.

### B1 — role witnesses and local families; Gate B

- `Tail.RoleWitness`
- `Tail.LocalFamilies`

CERT-F supplies the single global conflict graph, quota packing, disjoint
roles, regular-epimorphic witness projection, local folds, and resource
majorants.

Checkpoint: `gate-B`.

### T — aggregation and binary tail; Gate T

- `Tail.ResourceBounds`
- `Tail.GradeAggregation`
- `Tail.Provider`

CERT-G fixes the dependent grade intervals, uniform lower endpoint,
comparable-band width, cross-witness overlap, convergent resource series, and
vanishing tail. Then construct the free profile path and arbitrary-obstacle
binary tail with the exact binder-level signature.

Checkpoint: `gate-T`.

### E — ordinary exact realization; Gate E

- `Exact.CofinalRealization`
- `Exact.ExactSpectrum`

Apply prefix-tail composition, least-absorber annihilation, literalization in
the interval `(0,2)`, grade translation, and exact-spectrum transfer exactly as
specified.

Checkpoint: `gate-E`.

### D — defect extension; Gate D

- `Defect.Quotient`
- `Defect.MasterSlab`
- `Defect.Saturation`

Specialize the universal profile quotient to ternary defect, translate the
fixed master-slab construction from CERT-H §H.6, apply one common binary tail,
then define the intrinsic minima and prove monotonicity.

Checkpoint: `gate-D`.

### F — final local release audit

1. Clean local build of every module and both public roots.
2. Verify the source import graph against `MODULE_IMPORTS.toml`.
3. Verify all 57 API owners and all 122 object declarations.
4. Re-run binder-level signature checks and all consumer smoke modules.
5. Run repository-wide placeholder and forbidden-surrogate scans.
6. Run the complete axioms audit and record exact toolchain/revision/digests.
7. Tag the final implementation commit only after all checks pass.

Checkpoint: `final-local-verified`.

Remote CI remains disabled through this checkpoint. Any one-time final remote
verification is a separate decision and never substitutes for these local
checks.

## 5. Change-control stop conditions

Implementation stops for user direction if any of the following occurs:

- a sealed public statement or binder cannot be expressed without changing its
  mathematical meaning;
- Mathlib 4.33.0 lacks a required result and following the fixed proof route
  would require a new mathematical lemma not already implicit in the sealed
  argument;
- the pinned Haxell source requires more than compatibility-only adaptation;
- two normative files disagree in a way that changes a declaration, proof
  route, witness, constant, or dependency;
- a requested change would weaken an exit criterion or replace a theorem by a
  finite computation or concrete instance.

Ordinary elaboration, namespace, coercion, import, API-discovery, and local
engineering choices are resolved without escalation.
