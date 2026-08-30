import Packing.RowedGraph

/-! Axiom and signature audit for `Packing.RowedGraph` (API-L-006). -/

#check @Erdos289.FiniteRowedGraph
#check @Erdos289.FiniteRowedGraph.rowFibre
#check @Erdos289.FiniteRowedGraph.rowCard
#check @Erdos289.FiniteRowedGraph.mem_rowFibre
#check @Erdos289.FiniteRowedGraph.mem_rowFibre_row
#check @Erdos289.FiniteRowedGraph.rowFibre_disjoint
#check @Erdos289.FiniteRowedGraph.rowFibre_cover
#check @Erdos289.FiniteRowedGraph.rowFibre_nonempty
#check @Erdos289.FiniteRowedGraph.rowCard_pos
#check @Erdos289.FiniteRowedGraph.sum_rowCard
#check @Erdos289.FiniteRowedGraph.IndepSubobject
#check @Erdos289.FiniteRowedGraph.IndependentTransversal
#check @Erdos289.FiniteRowedGraph.IndepSubobject.subset
#check @Erdos289.FiniteRowedGraph.IndependentTransversal.pick
#check @Erdos289.FiniteRowedGraph.IndependentTransversal.pick_spec
#check @Erdos289.FiniteRowedGraph.IndependentTransversal.pick_mem
#check @Erdos289.FiniteRowedGraph.IndependentTransversal.row_pick
#check @Erdos289.FiniteRowedGraph.IndependentTransversal.exists_mem_row
#check @Erdos289.FiniteRowedGraph.exists_independentTransversal_of_meets_rows
#check @Erdos289.FiniteRowedGraph.maxDegree_induce_le

#print axioms Erdos289.FiniteRowedGraph.rowFibre_disjoint
#print axioms Erdos289.FiniteRowedGraph.rowFibre_cover
#print axioms Erdos289.FiniteRowedGraph.sum_rowCard
#print axioms Erdos289.FiniteRowedGraph.IndependentTransversal.pick_spec
#print axioms Erdos289.FiniteRowedGraph.exists_independentTransversal_of_meets_rows
#print axioms Erdos289.FiniteRowedGraph.maxDegree_induce_le
