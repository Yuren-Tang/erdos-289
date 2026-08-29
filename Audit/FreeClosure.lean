import Universal.Profile.FreeClosure

open Erdos289

#check compactProfileObservationSystem
#check ObservationSystem.profileZeroSection
#check ObservationSystem.PhysWitness
#check ObservationSystem.PhysWitness.cover_regularEpi
#check ObservationSystem.PhysRaw
#check ObservationSystem.physRaw_resource_upper
#check ObservationSystem.Phys
#check pathTensor
#check pathRawLabels
#check pathTensor_coe
#check freePathProfile
#check freePathProfile_characterization
#check PathLabelTuple
#check PathLabelTuple.mem_pathRawLabels
#check PathLabelTuple.nonempty_of_mem_pathRawLabels
#check PathLabelTuple.mem_pathRawLabels_iff
#check PathwisePhysics
#check PathLabelTuple.toString
#check PathLabelTuple.toFamilies
#check PathLabelTuple.toString_composite
#check PathLabelTuple.sum_toPositionData_bound
#check PathLabelTuple.local_cover
#check PathLabelTuple.local_resource_bound
#check PathwisePhysicalCertificate
#check PathwiseCompositionData
#check PathwiseCompositionData.toPhysWitness
#check pathTensor_le_phys
#check pathTensor_le_phys_arrow
#check freePathProfile_le_phys

#print axioms ObservationSystem.physRaw_resource_upper
#print axioms ObservationSystem.physRaw_isClosed
#print axioms ObservationSystem.PhysWitness.cover_regularEpi
#print axioms pathTensor_le_phys
#print axioms PathLabelTuple.mem_pathRawLabels_iff
#print axioms PathLabelTuple.toString_composite
#print axioms PathLabelTuple.sum_toPositionData_bound
#print axioms PathwiseCompositionData.toPhysWitness
#print axioms freePathProfile_le_phys
