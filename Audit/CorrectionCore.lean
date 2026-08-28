import Universal.Correction.Core

open CategoryTheory
open Erdos289
open Erdos289.ObservationSystem

#check ObservationSystem.Correction
#check Correction.base
#check Correction.label
#check Correction.id
#check Correction.comp
#check Correction.comp_label
#check Correction.id_comp
#check Correction.comp_id
#check Correction.comp_assoc
#check ObservationSystem.Required
#check Required.condition
#check Required.sourceValue

#print axioms Correction.id_comp
#print axioms Correction.comp_id
#print axioms Correction.comp_assoc
#print axioms Required.condition
