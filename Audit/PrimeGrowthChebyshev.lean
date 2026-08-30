import PrimeGrowth.Chebyshev

/-! Axiom and signature audit for `PrimeGrowth.Chebyshev` (API-L-004). -/

#check @Erdos289.primeLogTheta
#check @Erdos289.primeLogPsi
#check @Erdos289.primeLogTheta_nonneg
#check @Erdos289.primeLogPsi_nonneg
#check @Erdos289.primeLogTheta_le_primeLogPsi
#check @Erdos289.primeLogTheta_mono
#check @Erdos289.primeLogPsi_ge
#check @Erdos289.primeLogTheta_le
#check @Erdos289.primeLogPsi_le
#check @Erdos289.primeLogPsi_sub_primeLogTheta_le
#check @Erdos289.primeLogTheta_ge
#check @Erdos289.PrimeLogBounds
#check @Erdos289.PrimeLogBounds.eventually_atTop
#check @Erdos289.primeLogBounds_exists
#check @Erdos289.primeLogTheta_isTheta

#print axioms Erdos289.primeLogTheta_nonneg
#print axioms Erdos289.primeLogTheta_mono
#print axioms Erdos289.primeLogPsi_ge
#print axioms Erdos289.primeLogTheta_le
#print axioms Erdos289.primeLogPsi_le
#print axioms Erdos289.primeLogPsi_sub_primeLogTheta_le
#print axioms Erdos289.primeLogTheta_ge
#print axioms Erdos289.PrimeLogBounds.eventually_atTop
#print axioms Erdos289.primeLogBounds_exists
#print axioms Erdos289.primeLogTheta_isTheta
