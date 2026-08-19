module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import AffineCorrection
public import Erdos289.PathSupport
public import Erdos289.PhysicalSupports
public import Erdos289.PrimePowerFiltration
public import Erdos289.TransverseReservoir
public import Erdos289.LocalProfiles
public import Erdos289.RestrictedFold
public import Erdos289.IndependentTransversal
public import Erdos289.DeformationFibres
public import Erdos289.PrimeSupplyAsymptotic
public import Erdos289.CyclicRow
public import Erdos289.CyclicStage
public import Erdos289.AtomClass
public import Erdos289.NeutralAtoms
public import Erdos289.LocalSystem
public import Erdos289.PaddedStage
public import Erdos289.PaddingBlocks
public import Erdos289.CurrentStage
public import Erdos289.IntervalBlocks
public import Erdos289.Statement
public import Erdos289.Literal
public import Erdos289.Descent
public import Erdos289.TailComposition
public import Erdos289.CoreSeed
public import Erdos289.ReciprocalObservation

import Erdos289.BadCarriers
import Erdos289.BinaryBlocks
import Erdos289.BinaryConfigurations
import Erdos289.ChunkPartition
import Erdos289.Composition
import Erdos289.ConflictDegree
import Erdos289.CostTail
import Erdos289.DeformationComposition
import Erdos289.EgyptianRefinement
import Erdos289.EndpointConfigurations
import Erdos289.GradeAggregation
import Erdos289.GradeInterval
import Erdos289.LightMobility
import Erdos289.NeutralConstruction
import Erdos289.PoolComposition
import Erdos289.PresentationComposition
import Erdos289.PrimeFibre
import Erdos289.PrimeRowFibre
import Erdos289.PrimeRowStage
import Erdos289.PrimeSupply
import Erdos289.ReciprocalIdentities
import Erdos289.ReservoirPacking
import Erdos289.RowCertificate
import Erdos289.RowReservoir
import Erdos289.RowSupply
import Erdos289.RowTruncation
import Erdos289.Selector
import Erdos289.SignedInverse
import Erdos289.SignedInverseAtom
import Erdos289.SignedInverseConflict
import Erdos289.SignedInverseReservoir
import Erdos289.SimpleFibre
import Erdos289.SquareFibre
import Erdos289.StageProfile
import Erdos289.StageToTail
import Erdos289.TernaryBlocks
import Erdos289.TernaryConfigurations
import Erdos289.UpperBlockification

/-!
# Erdős problem 289

The publication root.  The modules re-exported above are the deliberate public
surface: the intrinsic objects of the reciprocal system, the structural
theorems about them, the five external inputs, the descent spine, and the final
statements.  Everything else the package proves is a construction used to
establish those, and is imported here without being re-exported, so a consumer
of `Erdos289` sees the mathematics and not the machinery.

`Erdos289Test/` imports this root and nothing else, so the boundary is checked
by the build rather than asserted.
-/
