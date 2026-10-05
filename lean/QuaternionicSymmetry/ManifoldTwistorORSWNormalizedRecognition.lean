import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorORSWRecognitionApplication
import QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardHomogeneity
import QuaternionicSymmetry.ManifoldTwistorFullAutHomogeneityGeneration
import QuaternionicSymmetry.ManifoldTwistorORSWFixedWeightComparison
import QuaternionicSymmetry.ManifoldTwistorORSWSeedApplication
import QuaternionicSymmetry.ManifoldTwistorORSWCompactRealFormApplication
import QuaternionicSymmetry.ManifoldQuaternionicIsometryLieFromSources
import QuaternionicSymmetry.ManifoldTwistorPicardContactLieAction
import QuaternionicSymmetry.HolomorphicLineCoreSheafPicardGenerator

/-! Actual ORSW5.1 application with all real and complex group atlases and
the compact real form selected internally. The same compact maximal torus,
actual unpowered vertical weights and literal extremal components are used.
Extremal isolation remains explicit for the separate induction proof. -/
namespace QuaternionicSymmetry.ManifoldTwistorORSWNormalizedRecognition

open GeneralContactFanoORSWRecognitionSource ManifoldTwistorORSWFixedWeightComparison
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicActualWeightHull ManifoldQuaternionicVerticalCircleCharacter
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
open ManifoldTwistorORSWRecognitionApplication
open ManifoldTwistorPositiveRicciInput ManifoldTwistorPositiveContactAmple
open GeneralContactFanoPicardHomogeneitySource
open ManifoldTwistorBKKAnalyticPicardApplication ManifoldTwistorFullAutHomogeneityGeneration
open GeneralHolomorphicTransitiveOrbitSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [PreconnectedSpace M] [T3Space M]

/-- The actual maximal-torus pointness output closes both BKK branches and
the Picard recognition branch, retaining full homogeneity for induction. -/
theorem exists_normalized_homogeneous_generated_ample_of_extreme_isolation
    (hORSW : AnalyticCompactRealFormExtremalRecognition)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hCompact : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (hLeeOrbit : LeeHolomorphicTransitiveOrbitSubmersion)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      ManifoldQuaternionicScalarCurvature.localScalarCurvature
        P.tangent P.connection p y hy = 16 * (n : ℝ) * ((n : ℝ)+2))
    {r : ℕ} (T : CompactLieTorusInputs.TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hr : 2 ≤ r) (hMax : T.IsMaximal (QuaternionicIsometries P.tangent))
    (hIso : ∀ (z : SphereBundleTotal P.tangent)
      (hz : ∀ t, (actionOfEmbedding P.tangent T).representation t • z = z)
      (μ : Fin r → ℤ),
      (∀ t, torusVerticalCircleCharacter P.tangent hR3
        (actionOfEmbedding P.tangent T) z hz t = weightCharacter μ t) →
      (fun i => (μ i : ℝ)) ∈
        (convexHull ℝ (actualRealWeights P.tangent hR3
          (actionOfEmbedding P.tangent T))).extremePoints ℝ →
      (component P.tangent (actionOfEmbedding P.tangent T) z).Subsingleton) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
        letI := A.charts
        letI := A.complexManifold
        AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore P.tangent P.connection C.contact.line) ∧
        HolomorphicLineCorePullback.GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore P.tangent P.connection C.contact.line) ∧
        (∀ z w : SphereBundleTotal P.tangent,
          ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
            f.1 z = w) ∧
        (∀ z w : SphereBundleTotal P.tangent,
          ∃ f : TwistorHolomorphicAutomorphisms P.tangent P.connection A,
            f.1 z = w) := by
  obtain ⟨A,C,hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  have hAlt := analyticPicard_generator_or_contactAut_transitive
    hBKK P n (by omega) A C hAmple
  have hContact : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w := by
    rcases hAlt with hPic | hHom
    · exact contactAut_transitive_of_picard_extreme_isolation_from_sources
        hORSW hUnique hAutSource hNT hCompact hR3 hClosed hImm hLee
        P n hn hDim A C hAmple hPic T hr hMax hIso
    · exact hHom
  have hFull : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : TwistorHolomorphicAutomorphisms P.tangent P.connection A,
        f.1 z = w := by
    intro z w
    obtain ⟨f,hf⟩ := hContact z w
    exact ⟨contactForget P.tangent P.connection A C.contact.line f,hf⟩
  refine ⟨A,C,hAmple,?_,hContact,hFull⟩
  exact actual_contactLine_generated_of_contactAut_transitive_of_reductive
    hLeeOrbit hAutSource P A C hn hDim hContact

end
end QuaternionicSymmetry.ManifoldTwistorORSWNormalizedRecognition
