module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.SignedInverseReservoir
public import Erdos289.ConflictDegree

@[expose] public section

/-!
# The signed-inverse reservoir has constant conflict degree

Every candidate atom of a signed-inverse row is the binary block at its
distinguished start, so the general bound of `Erdos289/ConflictDegree.lean`
applies verbatim.  The bound depends only on the separation margin of the
physical constraint: not on the current prime power, and not on the row size.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/-- The distinguished start of a candidate, as a denominator. -/
def Candidate.start {Q p : ℕ} {c : PhysicalConstraint}
    (x : Candidate Q p c) (hQpos : 0 < Q) : Denominator :=
  ⟨x.pair.start x.orientation.sign, x.pair.start_pos hQpos x.orientation.sign⟩

theorem Candidate.support_eq_binaryBlock {Q p : ℕ} {c : PhysicalConstraint}
    (x : Candidate Q p c) (hQpos : 0 < Q) :
    x.support hQpos = binaryBlock (x.start hQpos) :=
  rfl

/-- A signed-inverse reservoir is an image of `binaryBlock`. -/
theorem reservoir_atoms_eq {Q p e : ℕ} {c : PhysicalConstraint}
    (A : Finset (Candidate Q p c)) (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e) :
    (reservoir A hp he hQ).atoms =
      (A.image fun x => x.start (hQ.symm ▸ pow_pos hp.pos e)).image binaryBlock := by
  classical
  rw [Finset.image_image]
  rfl

/-- Constant conflict degree of a signed-inverse row. -/
theorem reservoir_conflictNeighbors_card_le
    {Q p e : ℕ} {c : PhysicalConstraint}
    (A : Finset (Candidate Q p c)) (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    (a : Denominator) :
    ((reservoir A hp he hQ).conflictNeighbors (binaryBlock a)).card ≤
      2 * (max 1 c.separation + 1) := by
  classical
  exact TransverseReservoir.conflictNeighbors_card_le_of_binary
    (reservoir A hp he hQ) _ (reservoir_atoms_eq A hp he hQ) a

end SignedInverse
end Erdos289
