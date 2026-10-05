import QuaternionicSymmetry.ManifoldMaximalTorusContactExtension
import QuaternionicSymmetry.ManifoldSWMaximalTorus

/-! C12/E14 source-only existence of a faithful rank-at-least-two complex
contact torus on the actual twistor of a positive rescaling of the input
manifold. The same maximal compact isometry torus is retained. Normalization,
the dimension bound, compact maximal torus, complex action, faithfulness and
canonical section representation are all applied internally. This is not a
classification or maximality theorem for the complex contact group. -/

namespace QuaternionicSymmetry.ManifoldSWComplexContactTorus

open ManifoldMaximalTorusContactExtension ManifoldSWMaximalTorus
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldTwistorPositiveRicciInput HolomorphicPositiveLineKodairaSource
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput ManifoldRiemannianIsometryLieInput
open CompactLieTorusInputs ManifoldSWEquation22SourceContract
open ManifoldTwistorLeBrunComplexAtlas
open CompactTorusEigenbasisSource TorusCharacterInput
open ProjectiveAnalyticAlgebraicSources GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [T2Space M] [SecondCountableTopology M]
  (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

/-- C12 requires no Amann H1 input. The full-group route explicitly assumes preservation on the input
metric's homotheties; the output uses the actual positive metric rescaling. -/
theorem exists_c12_contact_torus_from_sources
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hQ : ∀ s hs, FullMetricSpanPreservation (rescaleCompact P s hs).tangent)
    (hMS : MyersSteenrodSource.{0,0})
    (hR3 : IsometryLieSource.{0,0})
    (hR4 : KillingLieSource.{0,0})
    (hTorus : MaximalTorusSource.{0,0})
    (hRankOne : CompactRankOneDimensionSource.{0,0})
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 12) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      HasFaithfulContactTorusExtension (rescaleCompact P s hs) S.quaternionicDimension := by
  letI : CompactSpace M := ⟨P.compact⟩
  obtain ⟨s, hs, hScalar⟩ := exists_normalized_scalar S P heq38 hn.1
  obtain ⟨r, hr, T, hMax⟩ := exists_maximal_torus_c12_from_sources S
    (rescaleCompact P s hs) hsource hsp heq38
    (complexContactExistence_of_positiveRicci hT1)
    hGeneral hEquation hCohom (hQ s hs) hMS hR3 hR4 hTorus hRankOne hn
  exact ⟨s, hs, contact_extension_of_maximal_torus
    hT1 hKodaira hR3 hFinite hEigen hCircle hLee
    (rescaleCompact P s hs) S.quaternionicDimension hn.1 S.real_finrank hScalar
    hr T hMax⟩

/-- E14 retains Amann's registered input separately and otherwise uses the
same actual geometric construction as C12. -/
theorem exists_e14_contact_torus_from_sources
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hQ : ∀ s hs, FullMetricSpanPreservation (rescaleCompact P s hs).tangent)
    (hMS : MyersSteenrodSource.{0,0})
    (hR3 : IsometryLieSource.{0,0})
    (hR4 : KillingLieSource.{0,0})
    (hTorus : MaximalTorusSource.{0,0})
    (hRankOne : CompactRankOneDimensionSource.{0,0})
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 14) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      HasFaithfulContactTorusExtension (rescaleCompact P s hs) S.quaternionicDimension := by
  letI : CompactSpace M := ⟨P.compact⟩
  obtain ⟨s, hs, hScalar⟩ := exists_normalized_scalar S P heq38 hn.1
  obtain ⟨r, hr, T, hMax⟩ := exists_maximal_torus_e14_from_sources S
    (rescaleCompact P s hs) hsource hAmann hsp heq38
    (complexContactExistence_of_positiveRicci hT1)
    hGeneral hEquation hCohom (hQ s hs) hMS hR3 hR4 hTorus hRankOne hn
  exact ⟨s, hs, contact_extension_of_maximal_torus
    hT1 hKodaira hR3 hFinite hEigen hCircle hLee
    (rescaleCompact P s hs) S.quaternionicDimension hn.1 S.real_finrank hScalar
    hr T hMax⟩

end
end QuaternionicSymmetry.ManifoldSWComplexContactTorus
