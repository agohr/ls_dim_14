import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorSelectedComponentRestrictionBound
import QuaternionicSymmetry.ManifoldTwistorSelectedNonzeroWeightBoundFromSources
import QuaternionicSymmetry.ManifoldPositiveQuaternionicWeightHull

/-! The source-derived nonzero Hamiltonian weight bound applies to the
literal restricted original contact line, conditional only on extension
surjectivity and the explicitly retained Lie hypotheses. -/
namespace QuaternionicSymmetry.ManifoldTwistorSelectedComponentRestrictionFromSources

open ManifoldTwistorSelectedComponentRestrictionBound
open ManifoldTwistorSelectedNonzeroWeightBoundFromSources
open ManifoldTwistorSelectedHamiltonianWeightSpaces
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldQuaternionicMaximalTorusAction ManifoldQuaternionicTorusAction
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicContactComponentRestriction
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open CompactTorusEigenbasisSource TorusCharacterInput
open GeneralUniqueContactHamiltonianSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open GeneralRealAdjointDifferentialSource GeneralKillingRadicalSource
open ManifoldTwistorNTContactInfinitesimalSource
open scoped Manifold ContDiff
noncomputable section

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [CompactSpace M] [PreconnectedSpace M] [LocallyCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

/-- The same literal full-torus component has at most one restricted
contact-line section if restriction is surjective. The zero-centre and
central-radical conditions remain premises, exactly as in the selected
root-space theorem; no BWW extension statement is hidden here. -/
theorem selected_restricted_finrank_le_one_from_sources
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hNTU : UniqueContactHamiltonianBijection)
    (hBG9 : LeeRealAdjointDifferentialSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hCompact : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness)
    (hBG : MaximalTorusLieCorrespondenceSource)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
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
    (hJoint : letI := A.charts; letI := A.complexManifold
      ContMDiff (𝓘(ℂ,VC).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms
          P.tangent P.connection A × SphereBundleTotal P.tangent => p.1.1 p.2))
    {r d : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent))
    (g : letI := hRealChart
      EmbeddedRealLieAtlas VR (Torus r) (QuaternionicIsometries P.tangent)
        T.hom d)
    (hRad : letI := A.charts; letI := A.complexManifold
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
    (hCenter : letI := A.charts; letI := A.complexManifold
      letI := contactCharts (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      letI := contactLieGroup (V := VC)
        P.tangent P.connection A C.contact.line hPreserve
      LieAlgebra.center ℂ (GroupLieAlgebra 𝓘(ℂ,VC)
        (ContactAutomorphisms P.tangent P.connection A C.contact.line)) = ⊥)
    (hAmple : letI := A.charts; letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (z : SphereBundleTotal P.tangent)
    (hz : ∀ t, (actionOfEmbedding P.tangent T).representation t • z = z)
    (ν : Fin r → ℤ)
    (hν : ∀ t, torusVerticalCircleCharacter P.tangent hR3
      (actionOfEmbedding P.tangent T) z hz t = weightCharacter ν t)
    (hν0 : ν ≠ 0)
    {b : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin b))
      (↥(component P.tangent (actionOfEmbedding P.tangent T) z))]
    (hIncl : letI := A.charts
      ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (Subtype.val : ↥(component P.tangent
          (actionOfEmbedding P.tangent T) z) → SphereBundleTotal P.tangent))
    (hSurj : Function.Surjective
      (contactRestriction P.tangent (actionOfEmbedding P.tangent T)
        P.connection A C.contact z hIncl)) :
    letI := A.charts
    Module.finrank ℂ (RestrictedGlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,EuclideanSpace ℂ (Fin b))
      (contactLineCore P.tangent P.connection C.contact.line)
      (Subtype.val : ↥(component P.tangent
        (actionOfEmbedding P.tangent T) z) → SphereBundleTotal P.tangent)
      hIncl) ≤ 1 := by
  have hBound := selected_nonzero_section_weight_finrank_le_one_from_sources
    hNT hNTU hBG9 hR3 hCompact hBG hClosed hImm hLee
    hFinite hEigen hCircle P n hn hDim A C hPreserve
    hRealChart hRealManifold hRealLie hJoint T hMax g hRad hCenter ν hν0
  exact restricted_finrank_le_one_of_selected_weight_bound
    P n A C T hR3 hFinite hEigen hCircle hAmple
    z hz ν hν hIncl hSurj hBound

end
end QuaternionicSymmetry.ManifoldTwistorSelectedComponentRestrictionFromSources
