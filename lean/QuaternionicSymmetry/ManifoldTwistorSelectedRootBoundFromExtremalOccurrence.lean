import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorSelectedCenterFromExtremalOccurrence
import QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightBoundFromSources

/-! The actual unpowered section-weight bound from geometric extremal
occurrence. Real weight span, character separation, centre zero and the
selected Cartan property are derived internally. Only the general sources,
actual ampleness, extremal occurrence and central radical remain explicit.
The occurrence input is upstream of, and independent of, this root bound. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedRootBoundFromExtremalOccurrence

open ManifoldTwistorSelectedCenterFromExtremalOccurrence
open ManifoldTwistorSelectedNonzeroWeightBoundFromSources
open ManifoldTwistorSelectedHamiltonianWeightSpaces
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

theorem selected_nonzero_section_weight_bound_of_extremal_occurrence
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
          ManifoldTwistorSelectedHamiltonianWeightSpaces.selectedSectionWeightSpace P n A C T ν ≠ ⊥)
    (hRad : letI := A.charts
      letI := A.complexManifold
      letI := contactCharts (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      letI := contactLieGroup (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      letI : LieGroup 𝓘(ℂ,VC) (minSmoothness ℂ 3)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
        LieGroup.of_le (ENat.LEInfty.out)
      LieAlgebra.HasCentralRadical ℂ
        (GroupLieAlgebra 𝓘(ℂ,VC)
          (ContactAutomorphisms P.tangent P.connection A C.contact.line)))
    (μ : Fin r → ℤ) (hμ : μ ≠ 0) :
    Module.finrank ℂ (selectedSectionWeightSpace P n A C T μ) ≤ 1 := by
  have hCenter := selected_contact_center_eq_bot_of_extremal_section_occurrence
    hNTU hBG9 hFinite hEigen hCircle
    hNT hR3 hCompact hBG hClosed hImm hLee
    P n hn hDim A C hPreserve hRealChart hRealManifold hRealLie
    hJoint T hMax g hAmple hVertices
  exact selected_nonzero_section_weight_finrank_le_one_from_sources
    hNT hNTU hBG9 hR3 hCompact hBG hClosed hImm hLee
    hFinite hEigen hCircle P n hn hDim A C hPreserve
    hRealChart hRealManifold hRealLie hJoint T hMax g hRad hCenter μ hμ

end
end QuaternionicSymmetry.ManifoldTwistorSelectedRootBoundFromExtremalOccurrence
