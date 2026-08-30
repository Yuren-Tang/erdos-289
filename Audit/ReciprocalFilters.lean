import Reciprocal.Filters

/-! Axiom and signature audit for `Reciprocal.Filters` (API-R0-005). -/

#check Erdos289.CurrentFilter
#check Erdos289.HeightOneCurrentFilter
#check Erdos289.EndpointIndexFilter
#check Erdos289.EndpointFilter
#check Erdos289.CurrentTail
#check Erdos289.CurrentTailFilter
#check Erdos289.exists_current_rank_ge
#check Erdos289.mem_currentFilter_iff
#check Erdos289.eventually_currentFilter_iff
#check Erdos289.currentFilter_neBot
#check Erdos289.tendsto_rank_atTop
#check Erdos289.tendsto_endpoint
#check Erdos289.eventually_le_endpoint
#check Erdos289.exists_currentTail_rank_ge
#check Erdos289.currentTailFilter_neBot
#check Erdos289.tendsto_currentTail
#check Erdos289.eventually_currentTailFilter_iff

#print axioms Erdos289.exists_current_rank_ge
#print axioms Erdos289.mem_currentFilter_iff
#print axioms Erdos289.currentFilter_neBot
#print axioms Erdos289.tendsto_rank_atTop
#print axioms Erdos289.tendsto_endpoint
#print axioms Erdos289.eventually_le_endpoint
#print axioms Erdos289.exists_currentTail_rank_ge
#print axioms Erdos289.currentTailFilter_neBot
#print axioms Erdos289.tendsto_currentTail
#print axioms Erdos289.eventually_currentTailFilter_iff
