# What this repository claims, and how to check it

## The claim

Two things are claimed, and they are different.

1. **Everything that builds is proved.** Every declaration in this package is
   either a definition or a theorem with a complete Lean proof term. There are
   no `sorry`s, no project axioms, and no `native_decide`.

2. **The unconditional Erdős 289 theorem is *not* claimed.** See `ROADMAP.md`
   for exactly which layers are missing. Do not read the list of proved
   theorems as a proof of the conjecture.

## Three independent checks

`lake build` succeeding does **not** mean the proof closure is free of
assumptions: a theorem can have a complete proof body and still depend
transitively on a `sorry` upstream. The three checks below are therefore
different in kind, and all three are run.

### 1. Source hygiene — local, syntactic

```bash
python3 scripts/source_scan.py
./scripts/import_scan.sh
./scripts/pin_scan.sh
```

Rejects `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
`implemented_by` and `extern` anywhere in the package; rejects a bare
`import Mathlib`; and checks that `lean-toolchain` and the pinned mathlib
revision name the same release. This is hygiene, not trust: it says nothing
about what the proofs depend on.

### 2. Transitive axiom audit — the actual trust check

`Audit.lean` pins the transitive axiom set of **every public declaration of the
package** with `#guard_msgs`. The only accepted dependencies are the ordinary
foundations inherited from mathlib:

```text
[propext, Classical.choice, Quot.sound]
```

Coverage is complete by construction, not by diligence. The audited set is not
a hand-maintained list: `scripts/public_decls.py` derives it from the sources —
every declaration in `Erdos289/` and `AffineCorrection/` that is not marked
`private` — and `scripts/gen_audit.py` regenerates `Audit.lean` from that set.
A new public theorem therefore cannot be added without also being audited, and
a wrong name cannot slip through either, because `#print axioms` on a name that
does not exist fails the build.

```bash
python3 scripts/gen_audit.py     # after adding or renaming a public declaration
```

Because the expected output is pinned rather than merely printed, a `sorryAx`
introduced by any future change — including one arriving through a dependency —
turns the build red instead of scrolling past in a log.

`Audit.lean` is a default build target, so

```bash
lake build
```

runs the audit.

### The publication surface

`Erdos289.lean` re-exports only the modules that carry the public mathematics:
the intrinsic objects, the structural theorems about them, the five external
inputs, the descent spine, and the final statements. The construction modules
are imported there without being re-exported, so a consumer of `Erdos289` sees
the mathematics and not the machinery. `Erdos289Test/` imports that root and
nothing else, so the boundary is checked by the build rather than asserted.

The audit is deliberately wider than the publication surface: it covers the
construction modules too.

### 3. External kernel replay — independent of the elaborator

The `.olean` files are produced by Lean's elaborator; checks 1 and 2 trust it.
`.github/workflows/kernel-check.yml` replays the whole environment through two
independent checkers:

* `leanchecker`, the reference external checker shipped with the toolchain;
* `nanoda`, an independent Lean 4 type checker written in Rust, run with
  `nanoda-allow-sorry: false`.

These re-check all of mathlib and are slow, so they run on tags, on a weekly
schedule, and on demand rather than on every push.

## Reproducing a build

The toolchain and every dependency revision are pinned. Do not run
`lake update`.

```bash
lake exe cache get   # mathlib oleans; building from source also works
lake build
```

Expected: `lean-toolchain` is `leanprover/lean4:v4.33.0` and `lake-manifest.json`
pins mathlib at its `v4.33.0` tag.

## External mathematics

Two Apache-2.0 developments are vendored rather than depended on, so that the
exact proved statements are visible in this repository and pinned by content
rather than by a floating branch. Upstream commits and the complete list of
local modifications are recorded in `THIRD_PARTY.md`. Their per-file copyright
notices are retained, and `NOTICE` reproduces the attributions.
