import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorNTContactInfinitesimalApplication

/-! Export the actual smoothness of the isometry-to-contact lift in the
SAME selected real isometry/complex contact atlases. The proof uses only
continuity of the literal lift and the registered general smooth-hom
theorem; it is not an added NT-C premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactLiftSmoothFromSources

open ManifoldTwistorContactAutomorphismTopology
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldPositiveQuaternionicKahlerGeometry
open ContinuousLieHomSmooth ComplexLieRealCompanion
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]

set_option maxHeartbeats 800000 in
theorem actual_contact_lift_smooth
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
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)] :
    letI := A.charts
    letI := A.complexManifold
    letI := hRealChart
    letI := hRealManifold
    letI := hRealLie
    letI := contactCharts (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    ContMDiff 𝓘(ℝ,VR) 𝓘(ℝ,VC) ∞
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
  exact continuous_hom_smooth
    (isometryContactLift P.tangent P.connection A C.contact.line)
    hClosed hImm hLee hContinuous

end
end QuaternionicSymmetry.ManifoldTwistorContactLiftSmoothFromSources
