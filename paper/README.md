# Paper workbench — post-PASS Erdős 289 rewrite

This branch is the publication-facing rewrite of the ordinary Erdős Problem 289 proof.

## Mathematical authority

The mathematical authority for this rewrite is the frozen closed-packet proof at commit

`f326a37fcb8957919a51d70498920fcfc6f86f62`

under `review/r40star-blind/`.  A fresh independent reviewer reconstructed the public theorem from that pinned directory only, using only the explicitly permitted Haxell independent-transversal theorem externally, and returned **PASS**.

The earlier pinned packet

`604f7ce759304533b1c06bea9a06f9f219421532`

received **INCOMPLETE — Minor Repair**; it is retained as provenance for the repaired WideStart/profile quantifier order, the `Lambda^2 B` transition cutoff, the full centre `gamma_B=alpha_B+beta_B`, and resource-before-first-hit ordering.

See `MATHEMATICAL_SEAL.md` for the authority boundary and the disposition of later R42/R43 mathematics-only packets.

## Active manuscript

`manuscript.tex` now proves only the ordinary E289 theorem, in the stronger physical subsystem where every interval has length 2 or 3.  The active proof spine is:

1. physical states and a partial/composable decorated-relation calculus;
2. the torsion filtration of `Q/Z`, prime-power currents, and the literal endpoint/current-step equality;
3. four ordinary inputs: remote neutral grade cubes, comparable prime bands, the restricted fixed-rank fold, and Haxell quota thinning;
4. deterministic signed-inverse rows with lower row scale, exact simple-value fibre bound, bounded conflict incidence, support scale, and summable resource;
5. a finite affine seed plus universal fixed-grade bridges and one neutral Hamming pullback, giving a WideStart of arbitrary `o(B/log B)` width with uniform survivor fraction and resource margin;
6. a local profile proved for **all sufficiently dense restrictions of the original signed-inverse row**, before any WideStart witness or Haxell packing is chosen;
7. target-only sponsored amortization: prime mints dominate cumulative composite debt, giving a final ray after the full centre `gamma_B` dies;
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

The older R16 files remain in the branch history and, for the moment, in the working tree, but they are **not referenced by `manuscript.tex` and are not active mathematical dependencies**.  In particular the publication proof does not use:

- `MasterSlab`;
- `DirectLTAR`;
- donor/predecessor allocation;
- target-specific filtered lifting;
- opposite-coset Tail exactification;
- the fixed component-profile `(b_2,b_3)` strengthening;
- the old atomic-convolution appendix.

These files may be removed from the publication tree later, after the post-PASS manuscript has compiled cleanly and the historical branch has been retained as provenance.

## Assurance and formalization status

The ordinary human-readable mathematics has an independent background-blind **PASS**.  The publication manuscript itself is a new editorial rewrite and still requires a manuscript-level audit for faithful transcription, notation, citations, LaTeX compilation, and exposition.

The Lean formalization remains separate and incomplete unless and until independently built and audited.  Large-language-model systems were used extensively in proof exploration, normalization, audit design, and manuscript preparation; the author remains responsible for the claims and presentation.
