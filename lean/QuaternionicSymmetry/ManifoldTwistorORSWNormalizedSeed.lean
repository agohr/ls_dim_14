import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldTwistorORSWSeedFromSources
import QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardHomogeneity
import QuaternionicSymmetry.ManifoldTwistorFullAutHomogeneityGeneration
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
namespace QuaternionicSymmetry.ManifoldTwistorORSWNormalizedSeed

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
open ManifoldTwistorORSWSeedFromSources
open ManifoldTwistorPositiveRicciInput ManifoldTwistorPositiveContactAmple
open GeneralContactFanoPicardHomogeneitySource
open ManifoldTwistorBKKAnalyticPicardApplication
open ManifoldTwistorFullAutHomogeneityGeneration
open GeneralHolomorphicTransitiveOrbitSource
open ManifoldTwistorORSWPicardSeed ManifoldSWEquation22SourceContract
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Both BKK exceptional branches and the Picard branch yield one actual
normalized homogeneous twistor and its same generated ample contact line. -/
theorem exists_normalized_homogeneous_generated_ample_seed
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
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (hLeeOrbit : LeeHolomorphicTransitiveOrbitSubmersion)
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hTorus : CompactLieTorusInputs.MaximalTorusSource.{0,0})
    (hRankOne : CompactLieTorusInputs.CompactRankOneDimensionSource.{0,0})    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      ManifoldQuaternionicScalarCurvature.localScalarCurvature
        P.tangent P.connection p y hy =
        16 * (S.quaternionicDimension : ℝ) * ((S.quaternionicDimension : ℝ) + 2)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection S.quaternionicDimension A,
        letI := A.charts
        letI := A.complexManifold
        AmpleCore 𝓘(ℂ,ComplexTwistorModel S.quaternionicDimension)
          (contactLineCore P.tangent P.connection C.contact.line) ∧
        HolomorphicLineCorePullback.GloballyGenerated
          𝓘(ℂ,ComplexTwistorModel S.quaternionicDimension)
          (contactLineCore P.tangent P.connection C.contact.line) ∧
        (∀ z w : SphereBundleTotal P.tangent,
          ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
            f.1 z = w) ∧
        (∀ z w : SphereBundleTotal P.tangent,
          ∃ f : TwistorHolomorphicAutomorphisms P.tangent P.connection A,
            f.1 z = w) := by
  obtain ⟨A,C,hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P S.quaternionicDimension hn S.real_finrank hScalar
  have hAlt := analyticPicard_generator_or_contactAut_transitive
    hBKK P S.quaternionicDimension (by omega) A C hAmple
  have hContact : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w := by
    rcases hAlt with hPic | hHom
    · exact contactAut_transitive_seed_from_sources
        hORSW hUnique hAutSource hNT hNTU hR3 hClosed hImm hLee S P hn hn7
        A C hAmple hPic hsource hsp heq38
        (complexContactExistence_of_positiveRicci hT1)
        hGeneral hEquation hCohom hTorus hRankOne
    · exact hHom
  have hFull : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : TwistorHolomorphicAutomorphisms P.tangent P.connection A,
        f.1 z = w := by
    intro z w
    obtain ⟨f,hf⟩ := hContact z w
    exact ⟨contactForget P.tangent P.connection A C.contact.line f,hf⟩
  refine ⟨A,C,hAmple,?_,hContact,hFull⟩
  exact actual_contactLine_generated_of_contactAut_transitive_of_reductive
    hLeeOrbit hAutSource P A C hn S.real_finrank hContact

end
end QuaternionicSymmetry.ManifoldTwistorORSWNormalizedSeed
