import QuaternionicSymmetry.ManifoldTwistorContactSectionRank
import QuaternionicSymmetry.ManifoldTwistorSelectedContactToralCartanFromSources
import QuaternionicSymmetry.CompactRealFormKilling
import QuaternionicSymmetry.ComplexLieToralDimension
import QuaternionicSymmetry.RankOneCartanDimension
import QuaternionicSymmetry.SelectedTorusAtlasDimensionUpper
import QuaternionicSymmetry.HolomorphicLineFiniteSectionsFromMathlib
import QuaternionicSymmetry.CompactTorusEigenbasisFromMathlib
import QuaternionicSymmetry.TorusCharacterFromMathlib

/-! The actual maximal-isometry-torus rank bound from the retained torus
Lie correspondence, the compact real form, and the internal root argument. -/
set_option maxHeartbeats 1200000
namespace QuaternionicSymmetry.ManifoldTwistorRankFromTorusLie
open QuaternionicSymmetry
open ManifoldTwistorContactSectionDimension
open ManifoldTwistorSelectedContactToralCartanFromSources
open ManifoldTwistorSelectedContactToralSelfCentralizingFromSources
open ManifoldTwistorSelectedContactToralLieSubalgebra
open ManifoldTwistorSelectedContactTorusSmooth
open CompactLieMaximalTorusTangentSource
open ComplexLieToralDifferentialSubalgebra

open GeneralUniqueContactHamiltonianSource
open ManifoldTwistorUniqueContactHamiltonianFromSources
open ManifoldTwistorContactContraction ManifoldTwistorContactInfinitesimalAction
open ManifoldTwistorLineCoreClasses HolomorphicLineCorePullback
open ManifoldQuaternionicSpanSymmetry CompactLieTorusInputs
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
open scoped Manifold ContDiff TensorProduct
noncomputable section

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]

theorem maximal_torus_of_contact_sections_from_torusLie
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hNTU : UniqueContactHamiltonianBijection)
    (hTorus : MaximalTorusSource.{0,0})
    (hBG : MaximalTorusLieCorrespondenceSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hCompact : CompactSpace (QuaternionicIsometries P.tangent))
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
            P.tangent P.connection A × SphereBundleTotal P.tangent => p.1.1 p.2))
    (hSections : 3 < Module.finrank ℂ
      (HolomorphicTwistSections P.tangent P.connection C.contact.line 1)) :
    ∃ r : ℕ, 2 ≤ r ∧ ∃ T : TorusEmbedding (QuaternionicIsometries P.tangent) r,
      T.IsMaximal (QuaternionicIsometries P.tangent) := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : CompactSpace (QuaternionicIsometries P.tangent) := hCompact
  letI : ChartedSpace VR (QuaternionicIsometries P.tangent) := hRealChart
  letI : IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealManifold
  letI : LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealLie
  letI : SecondCountableTopology (QuaternionicIsometries P.tangent) :=
    ChartedSpace.secondCountable_of_sigmaCompact VR _
  have heq := real_model_finrank_eq_contact_sections hNT hNTU hR3 hClosed hImm hLee
    P hCompact n hn hDim A C hPreserve hRealChart hRealManifold hRealLie hJoint
  have hV : 3 < Module.finrank ℝ VR := by
    rw [heq, ← twist_one_finrank_eq_contact_sections P n A C]
    exact hSections
  obtain ⟨r,hr,T,hMax⟩ := IdentityComponentMaximalTorus.exists_full_maximal_torus_of_dimension_pos
    VR (QuaternionicIsometries P.tangent) (by
      letI := IdentityComponentLie.charts VR (QuaternionicIsometries P.tangent)
      exact @hTorus VR (IdentityComponentLie.Component (QuaternionicIsometries P.tangent)) _ _ _ _ _)
    (by omega)
  refine ⟨r,?_,T,hMax⟩
  by_contra hsmall
  have hrle : r ≤ 1 := by omega
  obtain ⟨d,⟨g⟩⟩ := SelectedTorusEmbeddedLieAtlas.exists_selected_embedded_atlas (V := VR) T hClosed
  have hGlobal : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness :=
    ManifoldQuaternionicIsometryCompactness.compactness_of_isometryLie hR3
  have hCartan := selectedContactToralLie_isCartan_from_sources
    hNT hNTU RealAdjointDifferentialFromMathlib.realAdjointDifferential hR3 hGlobal
    hBG hClosed hImm hLee
    HolomorphicLineFiniteSectionsFromMathlib.compactHolomorphicLineSectionFiniteness
    CompactTorusEigenbasisFromMathlib.torusEigenbasisSource TorusCharacterFromMathlib.circleCharacterSource
    P n hn hDim A C hPreserve hRealChart hRealManifold hRealLie hJoint T hMax g
  have hSelf := selectedContactToralLie_selfCentralizing_from_sources
    hNT hR3 hGlobal hBG hClosed hImm hLee
    P n hn hDim A C hPreserve hRealChart hRealManifold hRealLie hJoint T hMax g
  have hBij := ManifoldTwistorNTContactInfinitesimalApplication.actual_contact_lift_complexified_bijective
    hNT hR3 hGlobal hClosed hImm hLee P n hn hDim A C hPreserve
    hRealChart hRealManifold hRealLie hJoint
  have hSmooth := ManifoldTwistorContactLiftSmoothFromSources.actual_contact_lift_smooth (VC := VC)
    hR3 hGlobal hClosed hImm hLee P n hn hDim A C hPreserve
    hRealChart hRealManifold hRealLie
  have hd := SelectedTorusAtlasDimensionUpper.selected_atlas_dim_le_rank T g hClosed hImm hLee
  letI := contactCharts (V := VC) P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := VC) P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := VC) P.tangent P.connection A C.contact.line hPreserve
  letI : SecondCountableTopology
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := by
    change SecondCountableTopology
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (ManifoldTwistorContactAutomorphisms.contactDistribution P.tangent P.connection A C.contact.line))
    infer_instance
  let H := toralLieSubalgebra (selectedContactTorusHom P n A C T)
    g.charts g.manifold g.lieGroup
    (selectedContactTorusHom_smooth (V := VC) hR3 hClosed hImm hLee P n A C hPreserve T
      g.charts g.manifold g.lieGroup)
  have hH : Module.finrank ℂ H ≤ 1 :=
    (ComplexLieToralDimension.toral_finrank_le _ _ _ _ _).trans (hd.trans hrle)
  let L := GroupLieAlgebra 𝓘(ℂ,VC) (ContactAutomorphisms P.tangent P.connection A C.contact.line)
  letI : FiniteDimensional ℂ L := by unfold L GroupLieAlgebra TangentSpace; infer_instance
  have hdimC : Module.finrank ℝ VR = Module.finrank ℂ L := by
    have h := (LinearEquiv.ofBijective _ hBij).finrank_eq
    rw [Module.finrank_baseChange] at h
    exact h
  have hCenter := RankOneCartanDimension.center_eq_bot_of_small_selfCentralizer H hH
    (by omega : 1 < Module.finrank ℂ L) hSelf
  letI : LieAlgebra.IsKilling ℂ L := CompactRealFormKilling.isKilling_of_compact_complexification
    (isometryContactLift P.tangent P.connection A C.contact.line) hSmooth hBij.2 hCenter
  letI : H.IsCartanSubalgebra := hCartan
  have hbound := RankOneCartanDimension.finrank_le_three_of_rank_one_cartan H hH
  change Module.finrank ℂ L ≤ 3 at hbound
  omega

/-- Both group atlases and compactness are now selected internally from
existing sources. Only the actual contact branch and section bound remain. -/
theorem maximal_torus_of_sections_from_torusLie
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hNTU : UniqueContactHamiltonianBijection)
    (hTorus : MaximalTorusSource.{0,0})
    (hBG : MaximalTorusLieCorrespondenceSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    (hSections : 3 < Module.finrank ℂ
      (HolomorphicTwistSections P.tangent P.connection C.contact.line 1)) :
    ∃ r : ℕ, 2 ≤ r ∧ ∃ T : TorusEmbedding (QuaternionicIsometries P.tangent) r,
      T.IsMaximal (QuaternionicIsometries P.tangent) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : PreconnectedSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : Nonempty (SphereBundleTotal P.tangent) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal P.tangent) := inferInstance
  have hCompact := ManifoldQuaternionicIsometryClosedSubgroup.quaternionicIsometries_compactSpace_of_isometryLie
    P.tangent (hR3 P.tangent)
  obtain ⟨d,hChartR,hManifoldR,hLieR,_hActionR⟩ :=
    ManifoldQuaternionicIsometryClosedSubgroup.exists_quaternionic_lie_atlas_of_isometryLie
      P.tangent (hR3 P.tangent) hClosed
  obtain ⟨VC,hNormC,hSpaceC,hFiniteC,hChartC,hManifoldC,hLieC,hJoint,_hRad⟩ :=
    hAutSource P n hn hDim A
  letI := hNormC
  letI := hSpaceC
  letI := hFiniteC
  letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChartC
  letI : IsManifold 𝓘(ℂ,VC) ∞ (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifoldC
  letI : LieGroup 𝓘(ℂ,VC) ∞ (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLieC
  exact maximal_torus_of_contact_sections_from_torusLie
    hNT hNTU hTorus hBG hR3 hClosed hImm hLee P hCompact n hn hDim
    A C hPreserve hChartR hManifoldR hLieR hJoint hSections


end
end QuaternionicSymmetry.ManifoldTwistorRankFromTorusLie
