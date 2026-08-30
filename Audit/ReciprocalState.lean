import Reciprocal.State

/-! Axiom and signature audit for `Reciprocal.State` (API-R0-001). -/

#check Erdos289.successorDist
#check Erdos289.successorGraph
#check Erdos289.allowedComponentTypes
#check Erdos289.E289State
#check Erdos289.E289Profile
#check Erdos289.stateProfile
#check Erdos289.gradeAugmentation
#check Erdos289.grade
#check Erdos289.reciprocalWeight
#check Erdos289.reciprocalValue
#check Erdos289.reciprocalValue_nonneg
#check Erdos289.reciprocalValuePos
#check Erdos289.reciprocalValuePos_unique
#check Erdos289.E289BinaryPhysicalDomain
#check Erdos289.E289NaryPhysicalDomain
#check Erdos289.e289PhysicalPartialMonoid
#check Erdos289.E289PhysicalFamily
#check Erdos289.E289FinitePhysicalFamily
#check Erdos289.stateProfile_naryUnion
#check Erdos289.grade_naryUnion
#check Erdos289.reciprocalValue_naryUnion
#check Erdos289.reciprocalValuePos_naryUnion
#check Erdos289.stateProfile_finitePhysicalUnion
#check Erdos289.grade_finitePhysicalUnion
#check Erdos289.reciprocalValue_finitePhysicalUnion
#check Erdos289.component_mem_uIcc
#check Erdos289.mem_support_of_mem_uIcc
#check Erdos289.componentCardinality_eq_two_or_three
#check Erdos289.PhysicalConstraint
#check Erdos289.ConstraintAdmissible
#check Erdos289.FamilyConstraintAdmissible
#check Erdos289.constraint_le_iff
#check Erdos289.constraintJoin
#check Erdos289.constraint_directed
#check Erdos289.completeSupport
#check Erdos289.completeSupport_finite
#check Erdos289.strengthen
#check Erdos289.le_strengthen
#check Erdos289.mem_strengthen_forbidden
#check Erdos289.strengthen_margin

#print axioms Erdos289.reciprocalValue_nonneg
#print axioms Erdos289.reciprocalValuePos_unique
#print axioms Erdos289.grade_naryUnion
#print axioms Erdos289.reciprocalValue_naryUnion
#print axioms Erdos289.reciprocalValuePos_naryUnion
#print axioms Erdos289.component_mem_uIcc
#print axioms Erdos289.mem_support_of_mem_uIcc
#print axioms Erdos289.componentCardinality_eq_two_or_three
#print axioms Erdos289.constraint_directed
#print axioms Erdos289.completeSupport_finite
#print axioms Erdos289.le_strengthen
#print axioms Erdos289.mem_strengthen_forbidden
