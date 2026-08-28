import Universal.Target.LeastAbsorber

/-! Axiom and signature audit for `Universal.Target.LeastAbsorber`. -/

open CategoryTheory.Limits
open QuotientAddGroup

namespace Erdos289

universe u

#check cyclicImage
#check leastAbsorberSubgroup
#check LeastAbsorber
#check leastAbsorber_compact
#check leastAbsorber_contains
#check leastAbsorber_exact
#check leastAbsorber_kills
#check leastAbsorber_le_iff
#check leastAbsorber_isInitial

#print axioms leastAbsorber_compact
#print axioms leastAbsorber_exact
#print axioms leastAbsorber_kills
#print axioms leastAbsorber_le_iff
#print axioms leastAbsorber_isInitial

end Erdos289
