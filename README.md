# Erdős Problem 289

Lean 4.33.0 / Mathlib 4.33.0 formalization of the sealed E289 construction
specification identified by SHA-256
`76b2ddd0797cea4d8614f1528c4a7f070c912d0a12418b5de9bd867a29142517`.

The production module tree follows the normative DAG in the sealed
specification.  Implementation work is translation only: changes to fixed
mathematical statements, binders, witnesses, constants, or proof routes require
a newly sealed specification.

## Build

```sh
lake exe cache get
lake build
```

In a managed container with restricted procfs executable discovery, use the
checked-in local wrapper instead.  It finds the pinned Lean installation (or
uses `LEAN_433_HOME`), rebuilds the small compatibility shim when necessary,
and runs Lake with the same local environment:

```sh
./e289 build
```

Individual audits use `./e289 lean Audit/Module.lean`; arbitrary Lake commands
use `./e289 lake ...`.  This wrapper is local build infrastructure only and
does not invoke remote CI.
