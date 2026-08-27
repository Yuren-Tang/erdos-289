import Universal.Asymptotics

/-! Axiom and signature audit for `Universal.Asymptotics`. -/

#check Erdos289.IsTheta
#check Erdos289.UniformSup
#check Erdos289.GradeFilter
#check Erdos289.ENNRealLittleO
#check Erdos289.UniformLittleO

#print axioms Erdos289.isTheta_refl
#print axioms Erdos289.isTheta_symm
#print axioms Erdos289.isTheta_trans
#print axioms Erdos289.isTheta_congr
#print axioms Erdos289.isTheta_mono_filter
#print axioms Erdos289.uniformSup_le_iff
#print axioms Erdos289.gradeFilter_neBot
#print axioms Erdos289.ENNRealLittleO.congr
#print axioms Erdos289.ENNRealLittleO.mono_left
#print axioms Erdos289.ENNRealLittleO.mono_right
#print axioms Erdos289.ENNRealLittleO.mono_filter
#print axioms Erdos289.uniformLittleO_iff_uniformSup
#print axioms Erdos289.nnreal_isLittleO_iff_ennrealLittleO
