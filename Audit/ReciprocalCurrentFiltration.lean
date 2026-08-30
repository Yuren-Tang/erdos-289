import Reciprocal.CurrentFiltration

/-! Axiom and signature audit for `Reciprocal.CurrentFiltration` (API-R0-004). -/

#check Erdos289.Current
#check Erdos289.Current.toSubgroup
#check Erdos289.Current.rank
#check Erdos289.Current.rank_pos
#check Erdos289.Current.toSubgroup_eq
#check Erdos289.Current.le_iff_rank_dvd
#check Erdos289.supIrred_iff_isPrimePow
#check Erdos289.Current.rank_isPrimePow
#check Erdos289.Current.exists_primePow
#check Erdos289.currentOfPrimePow
#check Erdos289.rank_currentOfPrimePow
#check Erdos289.current_equiv_primePower
#check Erdos289.Flt
#check Erdos289.F
#check Erdos289.Flt_le_H_factorial
#check Erdos289.isCompactElement_Flt
#check Erdos289.isCompactElement_F
#check Erdos289.Flt_le_F
#check Erdos289.le_Flt_of_rank_lt
#check Erdos289.not_le_Flt
#check Erdos289.SimpleFactor
#check Erdos289.NonzeroSimpleFactor
#check Erdos289.simpleFactorOrder
#check Erdos289.simpleFactorOrder_eq
#check Erdos289.simpleFactor_card_prime
#check Erdos289.simpleFactor_oneDimensional
#check Erdos289.Current.height
#check Erdos289.Current.height_eq
#check Erdos289.Current.height_pos
#check Erdos289.current_rank_eq_primePow_height
#check Erdos289.HigherCurrent
#check Erdos289.predecessor
#check Erdos289.predecessor_spec
#check Erdos289.predecessor_height
#check Erdos289.endpointSubgroup
#check Erdos289.endpointSubgroup_le_H_factorial
#check Erdos289.endpoint_finite
#check Erdos289.endpoint
#check Erdos289.endpointSubgroup_mono
#check Erdos289.endpoint_mono
#check Erdos289.endpoint_current_iff
#check Erdos289.compactSubgroupH_le_endpoint
#check Erdos289.endpoint_cofinal
#check Erdos289.Endpoint

#print axioms Erdos289.supIrred_iff_isPrimePow
#print axioms Erdos289.Current.rank_isPrimePow
#print axioms Erdos289.current_equiv_primePower
#print axioms Erdos289.isCompactElement_Flt
#print axioms Erdos289.isCompactElement_F
#print axioms Erdos289.not_le_Flt
#print axioms Erdos289.simpleFactorOrder_eq
#print axioms Erdos289.simpleFactor_card_prime
#print axioms Erdos289.simpleFactor_oneDimensional
#print axioms Erdos289.Current.height_eq
#print axioms Erdos289.current_rank_eq_primePow_height
#print axioms Erdos289.predecessor_spec
#print axioms Erdos289.predecessor_height
#print axioms Erdos289.endpoint_finite
#print axioms Erdos289.endpoint_mono
#print axioms Erdos289.endpoint_current_iff
#print axioms Erdos289.endpoint_cofinal
