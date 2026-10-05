import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorSelectedCenterFromSpanningWeights
import QuaternionicSymmetry.ManifoldQuaternionicContactFixedWeightSpan
import QuaternionicSymmetry.IntegralEigenbasisWeightOccurrence
import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusAction
namespace QuaternionicSymmetry.ManifoldTwistorSelectedCenterFromExtremalOccurrence

open ManifoldTwistorSelectedCenterFromSpanningWeights
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

theorem selected_contact_center_eq_bot_of_extremal_section_occurrence
    (hNTU : GeneralUniqueContactHamiltonianSource.UniqueContactHamiltonianBijection)
    (hBG9 : GeneralRealAdjointDifferentialSource.LeeRealAdjointDifferentialSource)
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hCircle : TorusCharacterInput.CircleCharacterSource)
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
        T.hom d)
    (hAmple : letI := A.charts; letI := A.complexManifold
      HolomorphicLineCoreAmpleFiniteMap.AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (ManifoldTwistorLineCoreClasses.contactLineCore P.tangent P.connection C.contact.line))
    (hVertices : letI : CompactSpace M := ⟨P.compact⟩
      letI : PreconnectedSpace M := ⟨P.connected⟩
      letI : LocallyCompactSpace M := inferInstance
      letI := A.charts
      ∀ w ∈ (convexHull ℝ (ManifoldQuaternionicActualWeightHull.actualRealWeights
          P.tangent hR3 (ManifoldQuaternionicMaximalTorusAction.actionOfEmbedding P.tangent T))).extremePoints ℝ,
        ∃ ν : Fin r → ℤ, TorusIntegralVertexExposure.realWeight ν = w ∧
          ManifoldTwistorSelectedHamiltonianWeightSpaces.selectedSectionWeightSpace P n A C T ν ≠ ⊥) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := VC)
      P.tangent P.connection A C.contact.line hPreserve
    LieAlgebra.center ℂ (GroupLieAlgebra 𝓘(ℂ,VC)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) = ⊥ := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI : LocallyCompactSpace M := inferInstance
  letI : ChartedSpace VR (QuaternionicIsometries P.tangent) := hRealChart
  letI : IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealManifold
  letI : LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealLie
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
  obtain ⟨b, μ, α, hWeight, hBracket, hCompat⟩ :=
    ManifoldTwistorSelectedComplexifiedCharactersFromSources.exists_selected_complexified_characters_from_sources
      hNTU hBG9 hR3 hClosed hImm hLee hFinite hEigen hCircle
      P n (by omega : 1 ≤ n) A C hPreserve hJoint T
      g.charts g.manifold g.lieGroup
  have hWFinite := ManifoldQuaternionicContactFixedWeightSpan.actualRealWeights_finite_from_sources
    P.tangent hR3 hFinite hEigen hCircle
    (ManifoldQuaternionicMaximalTorusAction.actionOfEmbedding P.tangent T)
    P.connection A C.contact hAmple
  have hWSpan := ManifoldQuaternionicContactFixedWeightSpan.actualRealWeights_span_eq_top_from_sources
    P.tangent hR3 hFinite hEigen hCircle
    (ManifoldQuaternionicMaximalTorusAction.actionOfEmbedding P.tangent T)
    (ManifoldQuaternionicMaximalTorusAction.actionOfEmbedding_faithful P.tangent T)
    P.connection A C.contact hAmple
  have hBasisSpan := IntegralEigenbasisWeightOccurrence.real_weight_span_of_extremal_occurrence
    (ManifoldTwistorSelectedHamiltonianWeightSpaces.selectedAdjointOperator (V := VC)
      P n A C hPreserve T) b μ (fun t i => hWeight i t)
    _ hWFinite hWSpan (by
      intro w hw
      obtain ⟨ν,hν,hSection⟩ := hVertices w hw
      refine ⟨ν,hν,?_⟩
      let e := ManifoldTwistorSelectedHamiltonianWeightSpaces.selectedHamiltonianWeightEquiv (V := VC)
        hNTU P n (by omega : 1 ≤ n) A C hPreserve hJoint T ν
      obtain ⟨s,hs,hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSection
      let v := e.symm ⟨s,hs⟩
      apply (Submodule.ne_bot_iff _).2
      refine ⟨(v : VC),v.property,?_⟩
      intro hv
      have hv' : v = 0 := Subtype.ext hv
      have hs' := congrArg e hv'
      have hs'' : (⟨s,hs⟩ : ManifoldTwistorSelectedHamiltonianWeightSpaces.selectedSectionWeightSpace
          P n A C T ν) = 0 := by simpa only [v, e.apply_symm_apply, map_zero] using hs'
      exact hs0 (congrArg Subtype.val hs''))
  exact selected_contact_center_eq_bot_of_spanning_basis
    hNT hR3 hCompact hBG hClosed hImm hLee
    P n hn hDim A C hPreserve hRealChart hRealManifold hRealLie
    hJoint T hMax g b μ α hBracket hCompat hBasisSpan

end
end QuaternionicSymmetry.ManifoldTwistorSelectedCenterFromExtremalOccurrence
