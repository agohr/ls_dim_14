import QuaternionicSymmetry.ManifoldSWTwoTorus
import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorus

/-! Conditional C12 and E14 maximal compact torus witnesses in the
actual quaternionic-isometry group, assuming full preservation for the supplied geometry. Maximality in the complex contact
automorphism group remains a distinct BWW comparison obligation. -/

namespace QuaternionicSymmetry.ManifoldSWMaximalTorus

open ManifoldPositiveQuaternionicKahlerGeometry ManifoldSWNormalizedKillingBound
open ManifoldSWTwoTorus ManifoldQuaternionicMaximalTorus
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput ManifoldRiemannianIsometryLieInput
open CompactLieTorusInputs ManifoldTwistorLeBrunComplexAtlas
open ManifoldSWEquation22SourceContract
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [T2Space M] [SecondCountableTopology M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem exists_maximal_torus_c12_from_sources
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
    ∃ r : ℕ, 2 ≤ r ∧
      ∃ T : TorusEmbedding (QuaternionicIsometries P.tangent) r,
        T.IsMaximal (QuaternionicIsometries P.tangent) := by
  letI : PreconnectedSpace M := ⟨P.connected⟩
  have hbound := killing_dimension_lower_bound_c12_from_sources S P
    hsource hsp heq38 hT1 hGeneral hEquation hCohom hn
  exact exists_maximal_torus_of_killing_dimension
    P.toPositiveQuaternionicKahlerGeometry
    S.quaternionicDimension hn.1 S.real_finrank hQ hMS hR3 hR4 hTorus hRankOne
    (lt_of_lt_of_le (delta_add_one_gt_three hn.1) hbound)

theorem exists_maximal_torus_e14_from_sources
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
    ∃ r : ℕ, 2 ≤ r ∧
      ∃ T : TorusEmbedding (QuaternionicIsometries P.tangent) r,
        T.IsMaximal (QuaternionicIsometries P.tangent) := by
  letI : PreconnectedSpace M := ⟨P.connected⟩
  have hbound := killing_dimension_lower_bound_from_sources S P
    hsource hAmann hsp heq38 hT1 hGeneral hEquation hCohom hn
  exact exists_maximal_torus_of_killing_dimension
    P.toPositiveQuaternionicKahlerGeometry
    S.quaternionicDimension hn.1 S.real_finrank hQ hMS hR3 hR4 hTorus hRankOne
    (lt_of_lt_of_le (delta_add_one_gt_three hn.1) hbound)

end
end QuaternionicSymmetry.ManifoldSWMaximalTorus
