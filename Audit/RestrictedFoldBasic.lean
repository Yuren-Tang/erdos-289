import RestrictedFold.Basic

/-! Axiom and signature audit for `RestrictedFold.Basic` (API-L-010). -/

#check @Erdos289.FinSub
#check @Erdos289.mem_finSub
#check @Erdos289.finSub_nonempty
#check @Erdos289.restrictedFold
#check @Erdos289.restrictedFoldImage
#check @Erdos289.mem_restrictedFoldImage
#check @Erdos289.restrictedFoldImage_nonempty
#check @Erdos289.restrictedFold_map
#check @Erdos289.finSub_map
#check @Erdos289.restrictedFoldImage_map
#check @Erdos289.card_restrictedFoldImage_map
#check @Erdos289.card_restrictedFoldImage_linearEquiv

#print axioms Erdos289.mem_finSub
#print axioms Erdos289.finSub_nonempty
#print axioms Erdos289.mem_restrictedFoldImage
#print axioms Erdos289.restrictedFold_map
#print axioms Erdos289.restrictedFoldImage_map
#print axioms Erdos289.card_restrictedFoldImage_linearEquiv
