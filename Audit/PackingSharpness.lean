import Packing.Sharpness

/-! Axiom and signature audit for `Packing.Sharpness` (API-L-008). -/

#check @Erdos289.graphSum
#check @Erdos289.isIndepSet_of_inl
#check @Erdos289.isIndepSet_of_inr
#check @Erdos289.graphSum_degree_inl
#check @Erdos289.graphSum_degree_inr
#check @Erdos289.maxDegree_graphSum_le
#check @Erdos289.FiniteRowedGraph.amalgamRow
#check @Erdos289.FiniteRowedGraph.amalgam
#check @Erdos289.FiniteRowedGraph.noIT_amalgam
#check @Erdos289.FiniteRowedGraph.amalgam_rowCard_inl
#check @Erdos289.FiniteRowedGraph.amalgam_rowCard_inr
#check @Erdos289.bipartiteGraph
#check @Erdos289.bipartiteGraph_degree
#check @Erdos289.bipartiteGraph_maxDegree
#check @Erdos289.completeBipartite
#check @Erdos289.completeBipartite_rowCard
#check @Erdos289.completeBipartite_noIT
#check @Erdos289.sharpNoIndependentTransversal

#print axioms Erdos289.maxDegree_graphSum_le
#print axioms Erdos289.FiniteRowedGraph.noIT_amalgam
#print axioms Erdos289.FiniteRowedGraph.amalgam_rowCard_inl
#print axioms Erdos289.FiniteRowedGraph.amalgam_rowCard_inr
#print axioms Erdos289.completeBipartite_rowCard
#print axioms Erdos289.completeBipartite_noIT
#print axioms Erdos289.sharpNoIndependentTransversal
