import PrimeGrowth.ComparableBands

/-! Axiom and signature audit for `PrimeGrowth.ComparableBands` (API-L-005). -/

#check @Erdos289.AdmissibleDilation
#check @Erdos289.AdmissibleDilation.val
#check @Erdos289.AdmissibleDilation.two_le
#check @Erdos289.AdmissibleDilation.upper_lt
#check @Erdos289.AdmissibleDilation.one_le
#check @Erdos289.AdmissibleDilation.pos
#check @Erdos289.admissibleDilation_regularEpi
#check @Erdos289.primeBand
#check @Erdos289.mem_primeBand
#check @Erdos289.primeLogTheta_sub_eq_sum
#check @Erdos289.card_primeBand_mul_log_le
#check @Erdos289.le_card_primeBand_mul_log
#check @Erdos289.primeShell_upperBound
#check @Erdos289.primeBand_card_asymp

#print axioms Erdos289.admissibleDilation_regularEpi
#print axioms Erdos289.primeLogTheta_sub_eq_sum
#print axioms Erdos289.card_primeBand_mul_log_le
#print axioms Erdos289.le_card_primeBand_mul_log
#print axioms Erdos289.primeShell_upperBound
#print axioms Erdos289.primeBand_card_asymp
