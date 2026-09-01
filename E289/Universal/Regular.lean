import Mathlib

/-!
Packet-v1 implementation of the Type-host regular-cover structural layer.

Packet bindings:
* U0-DESCENT      ↦ Erdos289.Packet.U0_DESCENT
* U0-COVER-FACTOR ↦ Erdos289.Packet.U0_COVER_FACTOR
-/

namespace Erdos289.Packet

/-- THM.U0.DESCENT: a surjective cover reflects the top subobject in `Type`. -/
theorem U0_DESCENT {W B : Type*} (p : W → B) (hp : Function.Surjective p)
    (S : Set B) (hTop : ∀ w, p w ∈ S) : S = Set.univ := by
  ext b
  constructor
  · intro _
    exact Set.mem_univ b
  · intro _
    obtain ⟨w, rfl⟩ := hp b
    exact hTop w

/-- THM.U0.COVER.FACTOR: a factor of a surjective composite is surjective. -/
theorem U0_COVER_FACTOR {W S B : Type*} (f : W → S) (q : S → B)
    (hcomp : Function.Surjective (q ∘ f)) : Function.Surjective q := by
  intro b
  obtain ⟨w, hw⟩ := hcomp b
  exact ⟨f w, hw⟩

end Erdos289.Packet
