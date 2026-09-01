import Mathlib

/-!
Packet-v1 finite-subobject cardinality fibration.

The base fibration is represented concretely by its display map

  Finset A → {h : ℕ // h ≤ Fintype.card A}.

Its fibre over h is therefore the ordinary fibre of this map.
-/

namespace Erdos289.Packet

universe u

/-- DEF.U1.FINSUBCARD: cardinality display for finite subobjects of a finite type. -/
noncomputable def U1_FINSUBCARD (A : Type u) [Fintype A] :
    Finset A → {h : ℕ // h ≤ Fintype.card A} := by
  classical
  intro T
  refine ⟨T.card, ?_⟩
  simpa using Finset.card_le_card (Finset.subset_univ T)

/-- THM.U1.FINSUBCARD.EPI: every cardinality in [0, |A|] has a finite subobject. -/
theorem U1_FINSUBCARD_EPI (A : Type u) [Fintype A] :
    Function.Surjective (U1_FINSUBCARD A) := by
  classical
  intro h
  have hh : h.1 ≤ (Finset.univ : Finset A).card := by
    simpa using h.2
  rcases Finset.powersetCard_nonempty.2 hh with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  apply Subtype.ext
  exact (Finset.mem_powersetCard.mp hT).2

end Erdos289.Packet
