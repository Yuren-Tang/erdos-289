import Universal.Target.CompactResolution

/-! Axiom and signature audit for `Universal.Target.CompactResolution`. -/

#check Erdos289.CompactStage
#check Erdos289.compactSubgroup_iff_finitelyGenerated
#check Erdos289.CompactStage.finiteJoin
#check Erdos289.CompactStage.finiteJoin_upperBounds
#synth CategoryTheory.IsFiltered (Erdos289.CompactStage
  (Erdos289.singletonMarking (Γ := ℤ) 0))
#check Erdos289.compactResolutionTransition
#check Erdos289.compactResolution
#check Erdos289.compactResolutionObservation
#check Erdos289.compactResolution_eventually_zero
#check Erdos289.compactResolution_colimit_zero
#check Erdos289.compactStage_mapMarking
#check Erdos289.compactResolution_mapMarking

#print axioms Erdos289.compactSubgroup_iff_finitelyGenerated
#print axioms Erdos289.CompactStage.finiteJoin_upperBounds
#print axioms Erdos289.compactResolution
#print axioms Erdos289.compactResolutionObservation
#print axioms Erdos289.compactResolution_eventually_zero
#print axioms Erdos289.compactResolution_colimit_zero
#print axioms Erdos289.compactStage_mapMarking
#print axioms Erdos289.compactResolution_mapMarking
