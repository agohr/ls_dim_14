import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldTwistorORSWPicardSeed
import QuaternionicSymmetry.ManifoldSWTwoTorus
import QuaternionicSymmetry.ManifoldTwistorNTContactInfinitesimalSource
import QuaternionicSymmetry.ManifoldTwistorSelectedContactTorusSmooth
import QuaternionicSymmetry.ManifoldTwistorUniqueContactHamiltonianFromSources
import QuaternionicSymmetry.IdentityComponentMaximalTorus
import QuaternionicSymmetry.ManifoldTwistorHolomorphicSections
import QuaternionicSymmetry.ManifoldQuaternionicIsometryClosedFromAction

/-! Rank bounds for the actual quaternionic isometry group from contact
sections. The compact Lie group is constructed as a closed subgroup; NT
identifies its complexified Lie algebra with contact sections. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace QuaternionicSymmetry.ManifoldTwistorContactSectionDimension
open QuaternionicSymmetry

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

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]

theorem powerCore_one {B ι : Type*} [TopologicalSpace B]
    (Z : VectorBundleCore ℂ B ℂ ι) :
    HolomorphicLinePowers.powerCore Z 1 = Z := by
  have hcoord : (HolomorphicLinePowers.powerCore Z 1).coordChange = Z.coordChange := by
    funext i j x
    apply ContinuousLinearMap.ext
    intro z
    simp only [HolomorphicLinePowers.powerCore, pow_one,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    exact (HolomorphicLinePowers.linear_apply_one (Z.coordChange i j x) z).symm
  cases Z
  dsimp only [HolomorphicLinePowers.powerCore] at hcoord ⊢
  congr 1

theorem twist_one_finrank_eq_contact_sections
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A) :
    letI := A.charts
    Module.finrank ℂ (HolomorphicTwistSections P.tangent P.connection C.contact.line 1) =
      Module.finrank ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line)) := by
  letI := A.charts
  have hc : C.contact.line.integerTwistCore P.tangent P.connection 1 = C.contact.line.core := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl,
      HolomorphicContactLine.integerTwistCore_natCast, powerCore_one]
  simp only [HolomorphicTwistSections, GlobalSections, contactLineCore]
  rw [hc]

set_option maxHeartbeats 800000 in
theorem real_model_finrank_eq_contact_sections
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hNTU : UniqueContactHamiltonianBijection)
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
            P.tangent P.connection A × SphereBundleTotal P.tangent => p.1.1 p.2)) :
    letI := A.charts
    letI := A.complexManifold
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
    Module.finrank ℝ VR =
      Module.finrank ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line)) := by
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
  letI : CompactSpace (QuaternionicIsometries P.tangent) := hCompact
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
  have hComplex := hNT P n hn hDim A C hPreserve hRealChart hRealManifold hRealLie
    hAutChart hAutManifold hAutLie hJoint hSmooth
  have hHamilton := contactHamiltonian_bijective_of_fullPreserves_atlas (V := VC)
    hNTU P n (by omega) A C hPreserve hJoint
  let f : GroupLieAlgebra 𝓘(ℝ,VR) (QuaternionicIsometries P.tangent) →ₗ[ℝ]
      GroupLieAlgebra 𝓘(ℂ,VC)
        (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC)
      (isometryContactLift P.tangent P.connection A C.contact.line) 1).toLinearMap
  let e := LinearEquiv.ofBijective (complexifiedMapComplex f) hComplex
  let h := (contraction P.tangent P.connection A C.contact).comp
    (contactInfinitesimalActionLinear (V := VC)
      P.tangent P.connection A C.contact.line
      (contact_joint_holomorphic_of_full (V := VC)
        P.tangent P.connection A C.contact.line hPreserve hJoint))
  let eH := LinearEquiv.ofBijective h hHamilton
  have heq := (e.trans eH).finrank_eq
  rw [Module.finrank_baseChange] at heq
  exact heq


theorem maximal_torus_of_contact_sections_without_full_preservation
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hNTU : UniqueContactHamiltonianBijection)
    (hTorus : MaximalTorusSource.{0,0})
    (hRankOne : CompactRankOneDimensionSource.{0,0})
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
  apply IdentityComponentMaximalTorus.exists_full_maximal_torus_of_dimension_gt_three
    VR (QuaternionicIsometries P.tangent) ?_ ?_ hV
  · letI := IdentityComponentLie.charts VR (QuaternionicIsometries P.tangent)
    exact @hTorus VR (IdentityComponentLie.Component (QuaternionicIsometries P.tangent)) _ _ _ _ _
  · letI := IdentityComponentLie.charts VR (QuaternionicIsometries P.tangent)
    exact @hRankOne VR (IdentityComponentLie.Component (QuaternionicIsometries P.tangent)) _ _ _ _ _


end
end QuaternionicSymmetry.ManifoldTwistorContactSectionDimension
namespace QuaternionicSymmetry.ManifoldTwistorContactSectionMaximalTorus
open QuaternionicSymmetry Manifold
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicSpanSymmetry
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorUniqueContactFullEquiv ManifoldTwistorFullAutomorphisms
open ManifoldTwistorNTContactInfinitesimalSource GeneralUniqueContactHamiltonianSource
open GeneralHolomorphicFullAutomorphismLieSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource CompactLieTorusInputs
open ManifoldRiemannianMyersSteenrodInput ManifoldRiemannianIsometryLieInput
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Both group atlases and compactness are now selected internally from
existing sources. Only the actual contact branch and section bound remain. -/
theorem maximal_torus_of_sections_from_existing_sources
    (hR3 : IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hNTU : UniqueContactHamiltonianBijection)
    (hTorus : MaximalTorusSource.{0,0})
    (hRankOne : CompactRankOneDimensionSource.{0,0})
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
  exact ManifoldTwistorContactSectionDimension.maximal_torus_of_contact_sections_without_full_preservation
    hNT hNTU hTorus hRankOne hR3 hClosed hImm hLee P hCompact n hn hDim
    A C hPreserve hChartR hManifoldR hLieR hJoint hSections

end
end QuaternionicSymmetry.ManifoldTwistorContactSectionMaximalTorus

namespace QuaternionicSymmetry.ManifoldTwistorNumericalPicardSeed

open QuaternionicSymmetry
open CategoryTheory TopologicalSpace
open ManifoldSWActualHilbertValues ManifoldPositiveQuaternionicKahlerAllVirtualBounds
open GeneralUniqueContactHamiltonianSource
open GeneralContactFanoORSWSource GeneralContactFanoPicardUniquenessSource
open GeneralHolomorphicFullAutomorphismLieSource
open ManifoldTwistorORSWSeedApplication ManifoldTwistorORSWCompactRealFormApplication
open ManifoldTwistorNTContactInfinitesimalSource
open ManifoldTwistorBKKPicardUniquenessApplication
open ManifoldTwistorUniqueContactFullEquiv ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLineCoreClasses ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open HolomorphicLineCoreAmpleFiniteMap HolomorphicLineCoreSheafPicardGenerator
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ManifoldTwistorORSWPicardSeed ManifoldSWEquation22SourceContract
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Convert the proved virtual characteristic-number positivity into an
actual contact-section bound, before any isometry-group comparison. -/
theorem contact_sections_gt_three_of_virtual_positive_of_canonical
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) (hn14 : S.quaternionicDimension ≤ 14)
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection S.quaternionicDimension A)
    (hCanonical : Nonempty (HolomorphicContactCanonicalIso P.tangent P.connection
      S.quaternionicDimension A C.contact.line))
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hpositive : letI : CompactSpace M := ⟨P.compact⟩
      0 < ManifoldTangentCharacterNumber.characteristicFunctional P.tangent P.connection
        S.quaternionicDimension (S.quaternionicDimension-1)
        (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega) (Characters.virtual S.quaternionicDimension)) :
    3 < Module.finrank ℂ
      (HolomorphicTwistSections P.tangent P.connection C.contact.line 1) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI := A.charts
  letI := A.complexManifold
  letI : HasSheafify (Opens.grothendieckTopology
      (TopCat.of (SphereBundleTotal P.tangent))) (ModuleCat.{0} ℂ) :=
    SheafComplexSheafification.topCatHasSheafify
      (TopCat.of (SphereBundleTotal P.tangent))
  letI : HasExt.{1} (TopCat.Sheaf (ModuleCat.{0} ℂ)
      (TopCat.of (SphereBundleTotal P.tangent))) := HasExt.standard _
  have hSW := hEquation S P A C
  have hH := hCohom P S.quaternionicDimension hn S.real_finrank A C hCanonical
  rcases hH with ⟨hfinite,hKodairaPositive,hKodairaNegative,hSerre,_hSalamon⟩
  have hvirtual := actual_virtual_eq_sections_sub_delta S P A C hSW
    ⟨hn,hn14⟩ hCanonical (Classical.choice inferInstance) hfinite
    (hKodairaPositive 0 (by omega)) (hKodairaPositive 1 (by omega))
    hKodairaNegative hSerre
  rw [hvirtual] at hpositive
  have hnat : QuaternionicSymmetry.delta S.quaternionicDimension <
      Module.finrank ℂ (HolomorphicTwistSections P.tangent P.connection
        C.contact.line 1) := by
    exact_mod_cast (show (QuaternionicSymmetry.delta S.quaternionicDimension : ℝ) <
      (Module.finrank ℂ (HolomorphicTwistSections P.tangent P.connection
        C.contact.line 1) : ℝ) by linarith)
  have hSections : 3 < Module.finrank ℂ
      (HolomorphicTwistSections P.tangent P.connection C.contact.line 1) := by
    have hdelta := ManifoldSWTwoTorus.delta_add_one_gt_three hn
    omega
  exact hSections

/-- Compatibility wrapper for the earlier universal-canonical API. -/
theorem contact_sections_gt_three_of_virtual_positive
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) (hn14 : S.quaternionicDimension ≤ 14)
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection S.quaternionicDimension A)
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hpositive : letI : CompactSpace M := ⟨P.compact⟩
      0 < ManifoldTangentCharacterNumber.characteristicFunctional P.tangent P.connection
        S.quaternionicDimension (S.quaternionicDimension-1)
        (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega) (Characters.virtual S.quaternionicDimension)) :
    3 < Module.finrank ℂ
      (HolomorphicTwistSections P.tangent P.connection C.contact.line 1) := by
  exact contact_sections_gt_three_of_virtual_positive_of_canonical S P hn hn14 A C
    (contactCanonicalIso_of_generalContact P.tangent P.connection hGeneral C)
    hEquation hCohom hpositive

end
end QuaternionicSymmetry.ManifoldTwistorNumericalPicardSeed
