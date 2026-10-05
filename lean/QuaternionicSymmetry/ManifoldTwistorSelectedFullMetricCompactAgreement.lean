import QuaternionicSymmetry.ManifoldTwistorComplexFullAutAction
import QuaternionicSymmetry.ManifoldQuaternionicSelectedTorusFullMetric
import QuaternionicSymmetry.ManifoldTwistorFullMetricIsometryComparison
import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusAction

/-! Exact compact-restriction comparison for the SAME selected torus:
the constructed complex action in full Aut agrees with the ordinary
metric-isometry identity-component lift after BG-Q1/Myers–Steenrod
transport. No derivative/holomorphicity claim is inferred yet. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedFullMetricCompactAgreement

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullAutomorphismIdentityComponent
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorComplexFullAutAction
open ManifoldQuaternionicSelectedTorusFullMetric
open ManifoldQuaternionicMaximalTorusAction
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open IdentityComponentLie TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
  (hQ : FullMetricSpanPreservation P.tangent)
  (hMS : MyersSteenrodSource.{0,0})
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (B : CompatibleComplexAtlas P.tangent D n)
  (L : HolomorphicContactLine P.tangent D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)

theorem fullMetricLift_selected_compact (t : Fin r → Circle) :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    ((fullMetricIdentityLift P n hn hDim hQ hMS D B L hR3)
      ((liftToComponent (M ≃ᵢ M)
        (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom t)).1 =
      ManifoldTwistorFullAutomorphismLift.isometryFullLift P.tangent D B L
        (T.hom t) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  let q : Component (QuaternionicIsometries P.tangent) :=
    (liftToComponent (QuaternionicIsometries P.tangent) T).hom t
  have hComp :
      (liftToComponent (M ≃ᵢ M)
        (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom t =
      (identityComponentEquiv P n hn hDim hQ hMS) q := by
    apply Subtype.ext
    rfl
  rw [hComp]
  have hNat := congrArg (fun φ : Component (QuaternionicIsometries P.tangent) →*
      Component (TwistorHolomorphicAutomorphisms P.tangent D B) => φ q)
    (fullMetricIdentityLift_comp_equiv P n hn hDim hQ hMS D B L hR3)
  have hNat' := congrArg Subtype.val hNat
  simpa only [MonoidHom.comp_apply, q] using hNat'

end
end QuaternionicSymmetry.ManifoldTwistorSelectedFullMetricCompactAgreement
