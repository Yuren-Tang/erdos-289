import Neutral.Fibres

/-! Axiom and signature audit for `Neutral.Fibres` (API-L-001, API-L-002). -/

#check @Erdos289.successorRun
#check @Erdos289.mem_successorRun
#check @Erdos289.runVertex
#check @Erdos289.runVertex_mem
#check @Erdos289.successorRun_finite
#check @Erdos289.RunFamily
#check @Erdos289.RunFamily.block
#check @Erdos289.RunFamily.support
#check @Erdos289.RunFamily.support_finite
#check @Erdos289.RunFamily.block_disjoint
#check @Erdos289.RunFamily.componentEquiv
#check @Erdos289.RunFamily.fibreEquiv
#check @Erdos289.RunFamily.componentCardinality_componentOfBlock
#check @Erdos289.RunFamily.supportEquiv
#check @Erdos289.RunFamily.componentCardinality_mem
#check @Erdos289.RunFamily.toState
#check @Erdos289.RunFamily.reciprocalValue_toState
#check @Erdos289.RunFamily.reciprocalValue_toState_range
#check @Erdos289.RunFamily.stateProfile_toState
#check @Erdos289.RunFamily.stateProfile_toState_eq
#check @Erdos289.RunFamily.grade_toState
#check @Erdos289.RunFamily.ofGap
#check @Erdos289.RunFamily.sep_of_gap
#check @Erdos289.RunFamily.forb_of_large
#check @Erdos289.RunFamily.constraintAdmissible_toState
#check @Erdos289.RunFamily.reciprocalValue_toState_le
#check @Erdos289.RunFamily.reciprocalValue_toState_pos

#check @Erdos289.binaryType
#check @Erdos289.ternaryType
#check @Erdos289.E289ProfileGroup
#check @Erdos289.profileToGroup
#check @Erdos289.gradeGenerator
#check @Erdos289.defectGenerator
#check @Erdos289.NeutralPair
#check @Erdos289.NeutralPair.profileDiff
#check @Erdos289.NeutralGradeFiber
#check @Erdos289.NeutralDefectFiber
#check @Erdos289.RemoteLight

#check @Erdos289.gradeLeftFamily
#check @Erdos289.gradeRightFamily
#check @Erdos289.gradeLeftState
#check @Erdos289.gradeRightState
#check @Erdos289.grade_value_eq
#check @Erdos289.defectLeftFamily
#check @Erdos289.defectRightFamily
#check @Erdos289.defectLeftState
#check @Erdos289.defectRightState
#check @Erdos289.defect_value_eq
#check @Erdos289.stateProfile_gradeLeft
#check @Erdos289.stateProfile_gradeRight
#check @Erdos289.stateProfile_defectLeft
#check @Erdos289.stateProfile_defectRight
#check @Erdos289.grade_profileDiff
#check @Erdos289.defect_profileDiff
#check @Erdos289.neutralFibres_remote_light

#print axioms Erdos289.RunFamily.componentEquiv
#print axioms Erdos289.RunFamily.fibreEquiv
#print axioms Erdos289.RunFamily.componentCardinality_componentOfBlock
#print axioms Erdos289.RunFamily.reciprocalValue_toState
#print axioms Erdos289.RunFamily.stateProfile_toState
#print axioms Erdos289.RunFamily.grade_toState
#print axioms Erdos289.RunFamily.constraintAdmissible_toState
#print axioms Erdos289.RunFamily.reciprocalValue_toState_le
#print axioms Erdos289.grade_value_eq
#print axioms Erdos289.defect_value_eq
#print axioms Erdos289.grade_profileDiff
#print axioms Erdos289.defect_profileDiff
#print axioms Erdos289.neutralFibres_remote_light
