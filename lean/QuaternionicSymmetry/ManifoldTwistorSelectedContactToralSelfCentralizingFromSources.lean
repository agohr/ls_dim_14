import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorSelectedContactToralSelfCentralizing
import QuaternionicSymmetry.ManifoldTwistorContactLiftSmoothFromSources
import QuaternionicSymmetry.ManifoldTwistorSelectedContactTorusSmooth
import QuaternionicSymmetry.ManifoldTwistorNTContactInfinitesimalApplication

/-! Source-only actual self-centralizer of the selected contact toral Lie
subalgebra. The same maximal quaternionic-isometry torus, projective
twistor atlas, transported contact atlas and real isometry atlas occur
in BG-L1 and NT-C. No Cartan or root-space conclusion is imported. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedContactToralSelfCentralizingFromSources

open ManifoldTwistorSelectedContactToralSelfCentralizing
open ManifoldTwistorContactLiftSmoothFromSources
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorNTContactInfinitesimalApplication
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ManifoldTwistorNTContactInfinitesimalSource
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
theorem selectedContactToralLie_selfCentralizing_from_sources
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hCompact : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness)
    (hBG : MaximalTorusLieCorrespondenceSource)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    (hRealChart : ChartedSpace VR (QuaternionicIsometries P.tangent))
    (hRealManifold : letI := hRealChart
      IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent))
    (hRealLie : letI := hRealChart
      LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent))
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
            P.tangent P.connection A × SphereBundleTotal P.tangent => p.1.1 p.2))
    {r d : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent))
    (g : letI := hRealChart
      EmbeddedRealLieAtlas VR (Torus r) (QuaternionicIsometries P.tangent)
        T.hom d) :
    letI := A.charts
    letI := A.complexManifold
    letI := hRealChart
    letI := hRealManifold
    letI := hRealLie
    letI := contactCharts (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    let H := selectedContactToralLieSubalgebra P n A C hPreserve T
      g.charts g.manifold g.lieGroup
      (selectedContactTorusHom_smooth (V := VC)
        hR3 hClosed hImm hLee P n A C hPreserve T
        g.charts g.manifold g.lieGroup)
    ∀ z : GroupLieAlgebra 𝓘(ℂ,VC)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line),
      z ∈ H ↔ ∀ w ∈ H, ⁅z,w⁆ = 0 := by
  exact selectedContactToralLie_selfCentralizing P n hn hDim
    hCompact hBG hImm hLee A C hPreserve
    hRealChart hRealManifold hRealLie T hMax g
    (actual_contact_lift_smooth hR3 hCompact hClosed hImm hLee
      P n hn hDim A C hPreserve hRealChart hRealManifold hRealLie)
    (selectedContactTorusHom_smooth (V := VC)
      hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup)
    (actual_contact_lift_complexified_bijective hNT hR3 hCompact
      hClosed hImm hLee P n hn hDim A C hPreserve
      hRealChart hRealManifold hRealLie hJoint)

end
end QuaternionicSymmetry.ManifoldTwistorSelectedContactToralSelfCentralizingFromSources
