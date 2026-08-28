#!/bin/sh
set -eu

project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
mathlib_dir=$project_dir/../mathlib4
expected_mathlib=db584cd6d46c92f209a44c0f1c829460d327499d

if [ ! -x "$project_dir/e289" ]; then
  echo "missing executable ./e289 wrapper" >&2
  exit 1
fi
if [ ! -d "$mathlib_dir/.git" ]; then
  echo "missing sibling Mathlib checkout at $mathlib_dir" >&2
  exit 1
fi
actual_mathlib=$(git -C "$mathlib_dir" rev-parse HEAD)
if [ "$actual_mathlib" != "$expected_mathlib" ]; then
  echo "Mathlib revision mismatch: expected $expected_mathlib, got $actual_mathlib" >&2
  exit 1
fi

cd "$project_dir"

# This materializes only the revisions locked by lake-manifest.json.  The e289
# wrapper installs the local Mathlib path override before Lake is invoked.
./e289 lake env lean --version

# Fetch official oleans for every Mathlib root imported by the current project;
# Lake then builds only Erdős 289 modules, not Mathlib from source.
./e289 lake exe cache get \
  Mathlib.Algebra.Group.Pointwise.Set.Basic \
  Mathlib.Algebra.Group.Subgroup.Basic \
  Mathlib.Analysis.Asymptotics.Theta \
  Mathlib.Analysis.Normed.Group.Real \
  Mathlib.Data.ENNReal.Basic \
  Mathlib.Data.ENNReal.Real \
  Mathlib.Algebra.Category.MonCat.Basic \
  Mathlib.CategoryTheory.Limits.Shapes.RegularMono \
  Mathlib.Data.Finsupp.Basic \
  Mathlib.Algebra.BigOperators.Group.Finset.Basic \
  Mathlib.Data.Fintype.Sum \
  Mathlib.Algebra.Category.Grp.Basic \
  Mathlib.Algebra.BigOperators.Finsupp.Basic \
  Mathlib.Algebra.Group.Nat.Hom \
  Mathlib.Data.Fintype.Card \
  Mathlib.Data.Fintype.Quotient \
  Mathlib.Data.PNat.Notation \
  Mathlib.Algebra.BigOperators.Fin \
  Mathlib.Data.Fintype.BigOperators \
  Mathlib.Data.Fintype.EquivFin \
  Mathlib.Data.Set.Finite.Lattice \
  Mathlib.CategoryTheory.Comma.Over.Basic \
  Mathlib.CategoryTheory.Types.Basic \
  Mathlib.Tactic.FinCases \
  Mathlib.CategoryTheory.Adjunction.Basic \
  Mathlib.Logic.Relation \
  Mathlib.Order.RelIso.Basic \
  Mathlib.GroupTheory.FreeAbelianGroup \
  Mathlib.GroupTheory.QuotientGroup.Basic \
  Mathlib.Algebra.Category.Grp.Zero \
  Mathlib.CategoryTheory.Filtered.Basic \
  Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects \
  Mathlib.Order.Bounds.OrderIso \
  Mathlib.RingTheory.Finiteness.Basic

if [ "$#" -gt 0 ]; then
  ./e289 build "$@"
fi
