import QuaternionicSymmetry.ManifoldTwistorSquaredCanonical
import QuaternionicSymmetry.ManifoldTwistorRankFromTorusLie
import QuaternionicSymmetry.ManifoldTwistorContactSectionRank
import QuaternionicSymmetry.Stage2IntrinsicSources
import QuaternionicSymmetry.ManifoldTwistorORSWRecognitionApplication
import QuaternionicSymmetry.ManifoldPositiveQuaternionicBWWExtremeIsolation
import QuaternionicSymmetry.ManifoldSWMaximalTorus
import QuaternionicSymmetry.ManifoldTwistorNormalizedPicardIsolation

/-! Actual-manifold contact homogeneity, assembled by strong induction from
explicit universally quantified literature inputs. C12 has no Amann input. -/
namespace QuaternionicSymmetry.Stage2ContactInduction

open Stage2ActualInduction Stage2IntrinsicSources
open ManifoldTwistorORSWNormalizedSeed
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorPositiveRicciInput ManifoldTwistorPositiveContactAmple
open ManifoldTwistorNittaTakeuchiPositiveRicciInput
open ManifoldQuaternionicScalarCurvature
open ManifoldTwistorBKKAnalyticPicardApplication
open ManifoldTwistorORSWRecognitionApplication ManifoldTwistorNormalizedPicardIsolation
open ManifoldQuaternionicSpanSymmetry CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

/-- Internal step on one actual maximal torus. The Picard and exceptional
branches use the same selected twistor atlas and contact quotient. -/
theorem contactHomogeneous_of_maximal
    (sources : Sources) (n : ℕ) (hn : 2 ≤ n)
    (hLower : ∀ m, 2 ≤ m → m < n → NormalizedContactHomogeneity m)
    {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [PreconnectedSpace M] [T3Space M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ)+2))
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hr : 2 ≤ r) (hMax : T.IsMaximal (QuaternionicIsometries P.tangent)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
        ∀ z w : SphereBundleTotal P.tangent,
          ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
            f.1 z = w := by
  obtain ⟨A,C,hAmple⟩ := exists_normalized_ample_contact_core
    (normalized_of_positive sources.positiveContact) sources.kodaira
    P n hn hDim hScalar
  rcases analyticPicard_generator_or_contactAut_transitive
      sources.picardAlternative P n (by omega) A C hAmple with hPic | hHom
  · have hIso := normalized_picard_extrema_are_points sources P n hn hDim
      A C hAmple hPic hScalar T hMax hr hLower
    exact ⟨A,C,contactAut_transitive_of_picard_extreme_isolation_from_sources
      sources.orswRecognition sources.unique sources.bwwReductive sources.ntComplexification
      sources.isometryCompactness sources.isometryLie
      sources.closedEmbedding sources.equivariantImmersion sources.embeddedRestriction
      P n hn hDim A C hAmple hPic T hr hMax hIso⟩
  · exact ⟨A,C,hHom⟩

/-- Every actual C12 induction step. The maximal torus is chosen internally
from the numerical source chain, which never receives Amann's sign input. -/
theorem normalizedContactHomogeneity_step_c12
    (sources : Sources) (n : ℕ) (hn2 : 2 ≤ n) (hn12 : n ≤ 12)
    (hLower : ∀ m, 2 ≤ m → m < n → NormalizedContactHomogeneity m) :
    NormalizedContactHomogeneity n := by
  intro E M hNorm hInner hFinite hNontrivial hTopology hT2 hSecond hNonempty hCharts hManifold P hDim hScalar
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let S := P.tangent.reduction.Q (achart E (Classical.choice ‹Nonempty M›))
  have hSn : S.quaternionicDimension = n := by
    have hS := S.real_finrank
    omega
  obtain ⟨A,C,hAmple⟩ := exists_normalized_ample_contact_core
    (normalized_of_positive sources.positiveContact) sources.kodaira
    P S.quaternionicDimension (by omega) S.real_finrank (by simpa only [hSn] using hScalar)
  rcases analyticPicard_generator_or_contactAut_transitive
      sources.picardAlternative P S.quaternionicDimension (by omega) A C hAmple with hPic | hHom
  · have hpositive := ManifoldPositiveQuaternionicKahlerAllVirtualBounds.virtual_positive_two_twelve
      S P sources.orbital sources.kswSp1 sources.kswDecomposition
      S.quaternionicDimension ⟨by omega,by omega⟩ rfl
    have hSections := ManifoldTwistorNumericalPicardSeed.contact_sections_gt_three_of_virtual_positive_of_canonical
      S P (by omega) (by omega) A C
      (ManifoldTwistorSquaredCanonical.canonicalIso_of_analyticGenerator P.tangent P.connection C hPic)
      sources.swEquation
      sources.swCohomology hpositive
    have hPreserve := ManifoldTwistorBKKPicardUniquenessApplication.fullPreservesContact_of_analyticPicard_generator
      sources.unique P S.quaternionicDimension (by omega) A C hAmple hPic
    obtain ⟨r,hr,T,hMax⟩ :=
      ManifoldTwistorRankFromTorusLie.maximal_torus_of_sections_from_torusLie
        sources.isometryLie sources.closedEmbedding
        sources.equivariantImmersion sources.embeddedRestriction sources.bwwReductive
        sources.ntComplexification sources.ntHamiltonian sources.maximalTorus sources.torusLie
        P S.quaternionicDimension (by omega) S.real_finrank A C hPreserve hSections
    exact contactHomogeneous_of_maximal sources n (by omega) hLower P hDim hScalar T hr hMax
  · subst n
    exact ⟨A,C,hHom⟩

/-- The E14 step has its additional sign source explicitly separated. -/
theorem normalizedContactHomogeneity_step_e14
    (sources : Sources) (hAmann : AmannInput)
    (n : ℕ) (hn2 : 2 ≤ n) (hn14 : n ≤ 14)
    (hLower : ∀ m, 2 ≤ m → m < n → NormalizedContactHomogeneity m) :
    NormalizedContactHomogeneity n := by
  intro E M hNorm hInner hFinite hNontrivial hTopology hT2 hSecond hNonempty hCharts hManifold P hDim hScalar
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let S := P.tangent.reduction.Q (achart E (Classical.choice ‹Nonempty M›))
  have hSn : S.quaternionicDimension = n := by
    have hS := S.real_finrank
    omega
  obtain ⟨A,C,hAmple⟩ := exists_normalized_ample_contact_core
    (normalized_of_positive sources.positiveContact) sources.kodaira
    P S.quaternionicDimension (by omega) S.real_finrank (by simpa only [hSn] using hScalar)
  rcases analyticPicard_generator_or_contactAut_transitive
      sources.picardAlternative P S.quaternionicDimension (by omega) A C hAmple with hPic | hHom
  · have hpositive := ManifoldPositiveQuaternionicKahlerAllVirtualBounds.virtual_positive_two_fourteen
      S P sources.orbital hAmann sources.kswSp1 sources.kswDecomposition
      S.quaternionicDimension ⟨by omega,by omega⟩ rfl
    have hSections := ManifoldTwistorNumericalPicardSeed.contact_sections_gt_three_of_virtual_positive_of_canonical
      S P (by omega) (by omega) A C
      (ManifoldTwistorSquaredCanonical.canonicalIso_of_analyticGenerator P.tangent P.connection C hPic)
      sources.swEquation
      sources.swCohomology hpositive
    have hPreserve := ManifoldTwistorBKKPicardUniquenessApplication.fullPreservesContact_of_analyticPicard_generator
      sources.unique P S.quaternionicDimension (by omega) A C hAmple hPic
    obtain ⟨r,hr,T,hMax⟩ :=
      ManifoldTwistorRankFromTorusLie.maximal_torus_of_sections_from_torusLie
        sources.isometryLie sources.closedEmbedding
        sources.equivariantImmersion sources.embeddedRestriction sources.bwwReductive
        sources.ntComplexification sources.ntHamiltonian sources.maximalTorus sources.torusLie
        P S.quaternionicDimension (by omega) S.real_finrank A C hPreserve hSections
    exact contactHomogeneous_of_maximal sources n (by omega) hLower P hDim hScalar T hr hMax
  · subst n
    exact ⟨A,C,hHom⟩

/-- Source-only contact homogeneity on all actual normalized geometries
in dimensions two through twelve. There is no closure/recognition premise. -/
theorem normalizedContactHomogeneity_c12 (sources : Sources) :
    ∀ n, 2 ≤ n → n ≤ 12 → NormalizedContactHomogeneity n :=
  through_bound_from_two 12 (normalizedContactHomogeneity_step_c12 sources)

/-- Separate extended contact homogeneity theorem, disclosing Amann's source. -/
theorem normalizedContactHomogeneity_e14 (sources : Sources) (hAmann : AmannInput) :
    ∀ n, 2 ≤ n → n ≤ 14 → NormalizedContactHomogeneity n :=
  through_bound_from_two 14 (normalizedContactHomogeneity_step_e14 sources hAmann)

/-- The former seed range now follows from the uniform induction. -/
theorem normalizedContactHomogeneity_seed
    (sources : Sources) (n : ℕ) (hn : 2 ≤ n) (hn7 : n ≤ 7) :
    NormalizedContactHomogeneity n :=
  normalizedContactHomogeneity_c12 sources n hn (by omega)

end
end QuaternionicSymmetry.Stage2ContactInduction
