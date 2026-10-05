import QuaternionicSymmetry.ManifoldSWNormalizedKillingBound
import QuaternionicSymmetry.ManifoldQuaternionicTwoTorus

/-! Source-facing actual quaternionic torus-rank bounds for C12 and E14.
The analytic density, index-to-Killing, compact Lie rank and Q-preservation
bridges are composed here; the output is a genuine faithful continuous
torus action, not a dimension or rank certificate supplied as input. -/
namespace QuaternionicSymmetry.ManifoldSWTwoTorus

open ManifoldPositiveQuaternionicKahlerGeometry ManifoldSWNormalizedKillingBound
open ManifoldQuaternionicTwoTorus ManifoldQuaternionicTorusAction
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput ManifoldRiemannianIsometryLieInput
open CompactLieTorusInputs ManifoldTwistorLeBrunComplexAtlas
open ManifoldSWEquation22SourceContract
open scoped Manifold ContDiff
noncomputable section

theorem delta_add_one_gt_three {n : ℕ} (hn : 2 ≤ n) :
    3 < QuaternionicSymmetry.delta n + 1 := by
  unfold QuaternionicSymmetry.delta
  split_ifs <;> omega

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [T2Space M] [SecondCountableTopology M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

/-- C12: no Amann intersection-form premise is needed. Full metric-isometry preservation is an explicit hypothesis on this
geometry; the final classification instead uses contact-section rank. -/
theorem has_two_torus_c12_from_sources
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedComplexContactExistence.{0,0})
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hQ : FullMetricSpanPreservation P.tangent)
    (hMS : MyersSteenrodSource.{0,0})
    (hR3 : IsometryLieSource.{0,0})
    (hR4 : KillingLieSource.{0,0})
    (hTorus : MaximalTorusSource.{0,0})
    (hRankOne : CompactRankOneDimensionSource.{0,0})
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 12) :
    HasTorusRankAtLeast P.tangent 2 := by
  letI : PreconnectedSpace M := ⟨P.connected⟩
  have hbound := killing_dimension_lower_bound_c12_from_sources S P
    hsource hsp heq38 hT1 hGeneral hEquation hCohom hn
  exact has_two_torus_of_killing_dimension P.toPositiveQuaternionicKahlerGeometry
    S.quaternionicDimension hn.1 S.real_finrank hQ hMS hR3 hR4 hTorus hRankOne
    (lt_of_lt_of_le (delta_add_one_gt_three hn.1) hbound)

/-- E14: Amann's sign input is used only in the extra dimensions 13–14
inside the numerical theorem. The symmetry construction is unchanged. -/
theorem has_two_torus_e14_from_sources
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedComplexContactExistence.{0,0})
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hQ : FullMetricSpanPreservation P.tangent)
    (hMS : MyersSteenrodSource.{0,0})
    (hR3 : IsometryLieSource.{0,0})
    (hR4 : KillingLieSource.{0,0})
    (hTorus : MaximalTorusSource.{0,0})
    (hRankOne : CompactRankOneDimensionSource.{0,0})
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 14) :
    HasTorusRankAtLeast P.tangent 2 := by
  letI : PreconnectedSpace M := ⟨P.connected⟩
  have hbound := killing_dimension_lower_bound_from_sources S P
    hsource hAmann hsp heq38 hT1 hGeneral hEquation hCohom hn
  exact has_two_torus_of_killing_dimension P.toPositiveQuaternionicKahlerGeometry
    S.quaternionicDimension hn.1 S.real_finrank hQ hMS hR3 hR4 hTorus hRankOne
    (lt_of_lt_of_le (delta_add_one_gt_three hn.1) hbound)

end
end QuaternionicSymmetry.ManifoldSWTwoTorus
