import Universal.Profile.BoundSaturation

open Erdos289

#check ResourceBoundLE
#check boundSaturation
#check boundSaturation_isNucleus
#check BoundProfile
#check boundProfileReflection
#check boundProfile_reflection
#check boundProfile_add_coe
#check boundProfile_add_sSup_distrib

section
variable (M U : Type*) [AddCommMonoid M] [AddCommMonoid U]
  [PartialOrder U] [IsOrderedAddMonoid U]
#synth CompleteLattice (BoundProfile M U)
#synth AddCommMonoid (BoundProfile M U)
#synth IsAddQuantale (BoundProfile M U)
end

#print axioms boundSaturation_isNucleus
#print axioms boundProfile_reflection
#print axioms boundProfile_add_sSup_distrib
