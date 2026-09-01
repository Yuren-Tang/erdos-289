import Mathlib

/-!
Packet-v1 implementation of the replay-only Tail epsilon certificate.

Packet binding:
* C-TAILEPS ↦ Erdos289.Packet.C_TAILEPS

The exported packet node is the open positive-rational budget fibre itself.
The proof that it covers the terminal object is exposed separately; no
request-to-epsilon section is part of the packet API.
-/

namespace Erdos289.Packet

/-- CERT.C.TAILEPS: positive rational epsilon strictly below the supplied margin. -/
def C_TAILEPS (eta : {q : ℚ // 0 < q}) : Type :=
  {epsilon : {q : ℚ // 0 < q} // epsilon.1 < eta.1}

/-- The Tail epsilon certificate fibre is inhabited for every positive margin. -/
theorem C_TAILEPS_nonempty (eta : {q : ℚ // 0 < q}) :
    Nonempty (C_TAILEPS eta) := by
  refine ⟨⟨⟨eta.1 / 2, ?_⟩, ?_⟩⟩
  · positivity
  · nlinarith [eta.2]

/-- The certificate display to the terminal type is a cover in `Type`. -/
theorem C_TAILEPS_cover (eta : {q : ℚ // 0 < q}) :
    Function.Surjective (fun _ : C_TAILEPS eta => Unit.unit) := by
  intro u
  rcases C_TAILEPS_nonempty eta with ⟨epsilon⟩
  exact ⟨epsilon, Subsingleton.elim _ _⟩

end Erdos289.Packet
