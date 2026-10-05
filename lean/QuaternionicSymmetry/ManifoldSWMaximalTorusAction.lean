import QuaternionicSymmetry.ManifoldSWMaximalTorus
import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusAction

/-! The C12/E14 maximal compact torus and its faithful continuous action
are the same concrete embedding. The maximality assertion concerns actual
quaternionic isometries, not the larger complex-contact automorphism group. -/

namespace QuaternionicSymmetry.ManifoldSWMaximalTorusAction

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldSWMaximalTorus ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
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

theorem exists_maximal_action_c12_from_sources
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
        T.IsMaximal (QuaternionicIsometries P.tangent) ∧
          ∃ A : ContinuousTorusAction P.tangent r,
            A.Faithful ∧ A.representation = T.hom := by
  obtain ⟨r, hr, T, hMax⟩ := exists_maximal_torus_c12_from_sources S P
    hsource hsp heq38 hT1 hGeneral hEquation hCohom hQ hMS hR3 hR4
    hTorus hRankOne hn
  exact ⟨r, hr, T, hMax, actionOfEmbedding P.tangent T,
    actionOfEmbedding_faithful P.tangent T, rfl⟩

theorem exists_maximal_action_e14_from_sources
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
        T.IsMaximal (QuaternionicIsometries P.tangent) ∧
          ∃ A : ContinuousTorusAction P.tangent r,
            A.Faithful ∧ A.representation = T.hom := by
  obtain ⟨r, hr, T, hMax⟩ := exists_maximal_torus_e14_from_sources S P
    hsource hAmann hsp heq38 hT1 hGeneral hEquation hCohom hQ hMS hR3 hR4
    hTorus hRankOne hn
  exact ⟨r, hr, T, hMax, actionOfEmbedding P.tangent T,
    actionOfEmbedding_faithful P.tangent T, rfl⟩

end
end QuaternionicSymmetry.ManifoldSWMaximalTorusAction
