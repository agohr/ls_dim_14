import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorSelectedContactToralSelfCentralizingFromSources
import QuaternionicSymmetry.ManifoldTwistorSelectedCharacterSeparation
import QuaternionicSymmetry.SelectedTorusLieCenterFromSpanningWeights

/-! The centre of the actual contact Lie algebra vanishes from real spanning
of the SAME unpowered integral bracket eigenbasis weights. The actual
selected toral self-centralizer and complexified range are derived from
the general sources; no centre, Killing or root-multiplicity premise occurs. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedCenterFromSpanningWeights

open Module
open ManifoldTwistorSelectedContactToralSelfCentralizingFromSources
open ManifoldTwistorSelectedCharacterSeparation
open ManifoldTwistorSelectedTorusComplexifiedRange
open ManifoldTwistorSelectedTorusComplexifiedDifferential
open SelectedTorusLieCenterFromSpanningWeights
open IntegralWeightRealSpanComplexSeparation
open RealToComplexTangentComplexification TorusWeightCharacterDifferentialLinear
open ManifoldTwistorSelectedContactTorusSmooth
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorUniqueContactFullEquiv ManifoldTwistorUniqueContactFullLieTransfer
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

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem selected_contact_center_eq_bot_of_spanning_basis
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
    let L := GroupLieAlgebra 𝓘(ℂ,VC)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)
    let f := selectedTorusDifferentialIntoH (V := VC)
      hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup
    ∀ {ι : Type} (b : Basis ι ℂ L) (μ : ι → Fin r → ℤ)
      (α : ι → H →ₗ[ℂ] ℂ),
      (∀ (h : H) i, ⁅(h : L),b i⁆ = α i h • b i) →
      (∀ i, (α i).comp (complexifiedMapComplex f) =
        complexifiedMapComplex (weightCharacterDifferentialLinear (μ i) g.charts)) →
      Submodule.span ℝ (Set.range (fun i => realWeightVector (μ i))) = ⊤ →
      LieAlgebra.center ℂ L = ⊥ := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : ChartedSpace VR (QuaternionicIsometries P.tangent) := hRealChart
  letI : IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealManifold
  letI : LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealLie
  letI : CompactSpace (QuaternionicIsometries P.tangent) := by
    exact hCompact
      P.toPositiveQuaternionicKahlerGeometry n hn hDim
  letI : SecondCountableTopology (QuaternionicIsometries P.tangent) :=
    ChartedSpace.secondCountable_of_sigmaCompact VR _
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := VC)
    P.tangent P.connection A C.contact.line hPreserve
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.lieGroup
  dsimp only
  intro ι b μ α hBracket hCompat hSpan
  have hSelf := selectedContactToralLie_selfCentralizing_from_sources
    hNT hR3 hCompact hBG hClosed hImm hLee
    P n hn hDim A C hPreserve hRealChart hRealManifold hRealLie
    hJoint T hMax g
  exact center_eq_bot_of_selected_integral_basis T g hClosed hImm hLee _
    (fun z hz => (hSelf z).2 hz) _
    (selectedTorusDifferentialIntoH_complexified_surjective (V := VC)
      hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup)
    b μ α hBracket hCompat hSpan

end
end QuaternionicSymmetry.ManifoldTwistorSelectedCenterFromSpanningWeights
