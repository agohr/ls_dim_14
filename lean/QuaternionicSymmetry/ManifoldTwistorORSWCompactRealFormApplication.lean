import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.GeneralContactFanoORSWSource
import QuaternionicSymmetry.ManifoldTwistorNTContactInfinitesimalSource
import QuaternionicSymmetry.ManifoldTwistorSelectedContactTorusSmooth
import QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput

/-! The reviewed NT-C infinitesimal result and actual compactness of metric
isometries supply the literal compact-real-form criterion required by the
reviewed analytic ORSW corollary. This does not assert algebraic reductivity
or approve that external corollary. Smoothness uses the SAME contact atlas. -/

namespace QuaternionicSymmetry.ManifoldTwistorORSWCompactRealFormApplication

open ManifoldTwistorNTContactInfinitesimalSource
open ManifoldTwistorContactAutomorphismTopology
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldPositiveQuaternionicKahlerGeometry
open RealToComplexTangentComplexification
open ContinuousLieHomSmooth ComplexLieRealCompanion
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralContactFanoORSWSource
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]

set_option maxHeartbeats 800000 in
theorem actual_contact_lift_isCompactRealForm
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hCompact : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    (hRealChart : ChartedSpace VR
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent))
    (hRealManifold : letI := hRealChart
      IsManifold 𝓘(ℝ,VR) ∞
        (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent))
    (hRealLie : letI := hRealChart
      LieGroup 𝓘(ℝ,VR) ∞
        (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent))
    [hAutChart : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutManifold : IsManifold 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hAutLie : LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hJoint : letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,VC).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms
            P.tangent P.connection A × SphereBundleTotal P.tangent => p.1.1 p.2)) :
    letI := A.charts
    letI := A.complexManifold
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    letI : T3Space M := inferInstance
    letI : ChartedSpace VR
        (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
      hRealChart
    letI : IsManifold 𝓘(ℝ,VR) ∞
        (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
      hRealManifold
    letI : LieGroup 𝓘(ℝ,VR) ∞
        (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
      hRealLie
    letI := contactCharts (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    letI : CompactSpace
        (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
      hCompact
        P.toPositiveQuaternionicKahlerGeometry n hn hDim
    IsCompactRealForm (VR := VR) (VC := VC)
      (isometryContactLift P.tangent P.connection A C.contact.line) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : LocallyCompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal P.tangent) := inferInstance
  letI : ChartedSpace VR
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
    hRealChart
  letI : IsManifold 𝓘(ℝ,VR) ∞
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
    hRealManifold
  letI : LieGroup 𝓘(ℝ,VR) ∞
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
    hRealLie
  letI : CompactSpace
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) := by
    exact hCompact
      P.toPositiveQuaternionicKahlerGeometry n hn hDim
  letI : SecondCountableTopology
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
    ChartedSpace.secondCountable_of_sigmaCompact VR _
  letI := contactCharts (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI : IsManifold 𝓘(ℝ,VC) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := realManifold
  letI : LieGroup 𝓘(ℝ,VC) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := realLieGroup
  letI : SecondCountableTopology
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := by
    change SecondCountableTopology
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (contactDistribution P.tangent P.connection A C.contact.line))
    infer_instance
  have hContinuous : Continuous
      (isometryContactLift P.tangent P.connection A C.contact.line) :=
    isometryContactLift_continuous P.tangent P.connection A C.contact.line hR3
  have hSmooth : ContMDiff 𝓘(ℝ,VR) 𝓘(ℝ,VC) ∞
      (isometryContactLift P.tangent P.connection A C.contact.line) :=
    continuous_hom_smooth
      (isometryContactLift P.tangent P.connection A C.contact.line)
      hClosed hImm hLee hContinuous
  refine ⟨isometryContactLift_injective P.tangent P.connection A C.contact.line,
    hSmooth, ?_⟩
  exact hNT P n hn hDim A C hPreserve hRealChart hRealManifold hRealLie
    hAutChart hAutManifold hAutLie hJoint hSmooth

end
end QuaternionicSymmetry.ManifoldTwistorORSWCompactRealFormApplication
