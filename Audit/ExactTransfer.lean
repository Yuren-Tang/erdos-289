import Universal.Target.ExactTransfer

/-! Axiom and signature audit for `Universal.Target.ExactTransfer`. -/

open CategoryTheory

namespace Erdos289

#check compactResolutionObservationSystem
#check ObservationSystem.zeroSection
#check ObservationSystem.ExactMarkedFiber
#check ObservationSystem.ExactSpectrum
#check ObservationSystem.exactMarkedFiber_map
#check ObservationSystem.exactMarkedFiber_map_id
#check ObservationSystem.exactMarkedFiber_map_comp
#check ObservationSystem.exactSpectrum_mono_marking
#check ObservationSystem.TargetRealizer
#check ObservationSystem.TargetRealizer.projection_surjective
#check ObservationSystem.TargetRealizerFactorsThroughExactFiber
#check ObservationSystem.exactTransfer
#check ObservationSystem.exactTransfer_natural_marking
#check ObservationSystem.exactTransfer_singleton

#print axioms compactResolutionObservationSystem
#print axioms ObservationSystem.TargetRealizer.projection_surjective
#print axioms ObservationSystem.exactSpectrum_mono_marking
#print axioms ObservationSystem.exactTransfer
#print axioms ObservationSystem.exactTransfer_natural_marking
#print axioms ObservationSystem.exactTransfer_singleton

end Erdos289
