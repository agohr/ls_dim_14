import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldTwistorContactSectionRank
import QuaternionicSymmetry.ManifoldTwistorORSWPicardSeed
import QuaternionicSymmetry.ManifoldSWTwoTorus
import QuaternionicSymmetry.ManifoldTwistorORSWSeedApplication
import QuaternionicSymmetry.ManifoldTwistorORSWCompactRealFormApplication
import QuaternionicSymmetry.ManifoldQuaternionicIsometryLieFromSources
import QuaternionicSymmetry.ManifoldTwistorPicardContactLieAction
import QuaternionicSymmetry.HolomorphicLineCoreSheafPicardGenerator

/-! On the actual Picard branch, real and complex group atlases and the
compact real form are selected internally from the named general sources.
The torus rank is the actual rank predicate supplied by the numerical chain,
not an algebraic-group rank marker. The external ORSW derivation is reviewed in
Textbooks/STAGE2_SOURCE_REVIEW_20261001.md; final release audit is separate. -/
namespace QuaternionicSymmetry.ManifoldTwistorORSWSeedFromSources

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

/-- Actual seed contact homogeneity: every group atlas, compact real form
and rank-two torus is supplied internally by the named general sources. -/
theorem contactAut_transitive_seed_from_sources
    (hORSW : AnalyticCompactRealFormRankHomogeneity)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hNTU : GeneralUniqueContactHamiltonianSource.UniqueContactHamiltonianBijection)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) (hn7 : S.quaternionicDimension ≤ 7)
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection S.quaternionicDimension A)
    (hAmple : letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel S.quaternionicDimension)
        (contactLineCore P.tangent P.connection C.contact.line))
    (hPic : letI := A.charts
      letI := A.complexManifold
      Function.Bijective (fun q : ℤ =>
        (classMulEquiv 𝓘(ℂ,ComplexTwistorModel S.quaternionicDimension)
          (contactClass P.tangent P.connection C.contact.line) :
          SheafClass (B := SphereBundleTotal P.tangent)
            𝓘(ℂ,ComplexTwistorModel S.quaternionicDimension)) ^ q))
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedComplexContactExistence.{0,0})
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hTorus : CompactLieTorusInputs.MaximalTorusSource.{0,0})
    (hRankOne : CompactLieTorusInputs.CompactRankOneDimensionSource.{0,0}) :
    ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI := A.charts
  letI := A.complexManifold
  have hpositive := ManifoldPositiveQuaternionicKahlerAllVirtualBounds.virtual_positive_two_twelve
    S P hsource hsp heq38 S.quaternionicDimension ⟨hn,by omega⟩ rfl
  have hSections := ManifoldTwistorNumericalPicardSeed.contact_sections_gt_three_of_virtual_positive
    S P hn (by omega) A C hGeneral hEquation hCohom hpositive
  have hPreserve := fullPreservesContact_of_analyticPicard_generator
    hUnique P S.quaternionicDimension (by omega) A C hAmple hPic
  obtain ⟨r,hr,T,_hMax⟩ :=
    ManifoldTwistorContactSectionMaximalTorus.maximal_torus_of_sections_from_existing_sources
      hR3 hClosed hImm hLee hAutSource hNT hNTU hTorus hRankOne
      P S.quaternionicDimension hn S.real_finrank A C hPreserve hSections
  let T2 := T.restrictRank (QuaternionicIsometries P.tangent) hr
  have hRank : HasTorusRankAtLeast P.tangent 2 := by
    refine ⟨⟨T2.hom,?_⟩,T2.injective_hom⟩
    exact (ManifoldQuaternionicIsometryTopology.continuous_action P.tangent).comp
      ((T2.continuous_hom.comp continuous_fst).prodMk continuous_snd)
  exact ManifoldTwistorORSWPicardSeed.contactAut_transitive_of_picard_rank_two_from_sources
    hORSW hUnique hAutSource hNT hR3 hClosed hImm hLee
    P S.quaternionicDimension hn hn7 S.real_finrank A C hAmple hPic hRank

end
end QuaternionicSymmetry.ManifoldTwistorORSWSeedFromSources
