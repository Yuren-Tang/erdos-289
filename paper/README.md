# Paper workbench — post-PASS Erdős 289 rewrite

This branch is the publication-facing rewrite of the ordinary Erdős Problem 289 proof.

## Mathematical provenance

The core ordinary-E289 proof spine was reconstructed independently from the frozen background-blind proof at commit

`f326a37fcb8957919a51d70498920fcfc6f86f62`

and received **PASS**.  A later hostile review of the mathematics/engineering R44 packet found no central counterexample but identified three exact-interface defects relevant to the paper: the carrier cutoff type, the neutral resource-tolerance field, and an implicit top-homogeneous coefficient bridge in the restricted-fold proof.

The current manuscript incorporates the R45 mathematical exactifications for those points, plus the intrinsic bounded-lag sponsor lemma.  It does **not** import R45's engineering requirements as publication blockers, nor does it replace the cleaner universal dense-subrow profile by a narrower packing-dependent ontology.

See `MATHEMATICAL_SEAL.md` for the exact publication authority boundary.

## Active manuscript

`manuscript.tex` proves only the ordinary E289 theorem, in the stronger physical subsystem where every interval has length 2 or 3.  The active proof spine is:

1. physical states and a partial/composable decorated-relation calculus;
2. the torsion filtration of `Q/Z`, prime-power currents, and the literal endpoint/current-step equality;
3. four ordinary inputs: remote neutral grade cubes, comparable prime bands, the restricted fixed-rank fold, and Haxell quota thinning;
4. deterministic signed-inverse rows with exact natural carrier band, lower row scale, exact simple-value fibre bound, bounded conflict incidence, support scale, and summable resource;
5. a finite affine seed plus universal fixed-grade bridges and one neutral Hamming pullback, giving a WideStart of arbitrary `o(B/log B)` width with uniform survivor fraction and resource margin;
6. a local profile proved for **all sufficiently dense restrictions of the original signed-inverse row**, before any WideStart witness or Haxell packing is chosen;
7. target-only sponsored amortization using an intrinsic bounded-lag earlier prime sponsor, giving a final ray after the full centre `gamma_B` dies;
8. one finite Haxell packing only after a first-hit horizon is fixed, followed by genuine n-ary physical strictification and the `W<2` resource bound;
9. Set-level terminal pullbacks at `(0,k)` and literalization by `Q -> Q/Z`, giving `W=1`.

The active LaTeX files are:

- `sections/postpass-01-states-and-filtration.tex`
- `sections/postpass-02-auxiliary-inputs.tex`
- `sections/postpass-03-signed-inverse.tex`
- `sections/postpass-04-wide-start.tex`
- `sections/postpass-05-local-profile.tex`
- `sections/postpass-06-scalar-finality.tex`
- `sections/postpass-07-finite-realization.tex`
- `sections/postpass-08-terminalization.tex`
- `appendices/prime-supply.tex`
- `appendices/restricted-fold.tex`
- `appendices/prefix-seed.tex`

## Historical files

The older R16 files remain in the branch history and, for the moment, in the working tree, but they are **not referenced by `manuscript.tex` and are not active mathematical dependencies**.  In particular the publication proof does not use MasterSlab, DirectLTAR, donor/predecessor allocation, target-specific filtered lifting, opposite-coset Tail exactification, the fixed component-profile strengthening, or the old atomic-convolution appendix.

## Current gate

The manuscript has reproducible LaTeX CI and PDF generation.  After the R45 mathematical exactification reconciliation, the next gate is a fresh **manuscript-level independent review** of the exact PDF/source for faithful transcription, theorem-hypothesis/consumer consistency, notation, references, and exposition.

The Lean formalization remains a separate unfinished project.  Large-language-model systems were used extensively in proof exploration, normalization, source checking, and manuscript preparation; the author remains responsible for the claims and presentation.
