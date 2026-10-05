import QuaternionicSymmetry.ComplexTorusCompactCentralizer
import QuaternionicSymmetry.ManifoldTwistorSelectedIdentityAutCompactAgreement

/-! The actual complex contact action factors through the group centralizer
of the SAME selected compact ordinary-metric torus inside full Aut⁰. This
only identifies a closed group carrier, not its Lie atlas or maximality. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedMetricCentralizer

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorComplexIdentityAutAction
open ManifoldTwistorSelectedIdentityAutCompactAgreement
open ManifoldQuaternionicSelectedTorusFullMetric
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open IdentityComponentLie TorusLaurentRepresentation
open ComplexTorusCompactCentralizer
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
  (C : HolomorphicContactData P.tangent D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
  (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal P.tangent))
  (hJoint : letI := B.charts
    ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
      𝓘(ℂ, ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal P.tangent => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal P.tangent),
    ρ (compactInclusion r t) z =
      sphereTotalMap P.tangent
        ((actionOfEmbedding P.tangent T).representation t) z)

def selectedMetricCentralizer :
    Subgroup (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
  compactCentralizer (complexIdentityAutAction P.tangent D B C
    (actionOfEmbedding P.tangent T) ρ hJoint hRestrict)

theorem selectedMetricCentralizer_eq_metric :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    selectedMetricCentralizer P n D B C T
      ρ hJoint hRestrict =
      Subgroup.centralizer (Set.range
        ((fullMetricIdentityLift P n hn hDim hQ hMS D B C.line hR3).comp
          ((liftToComponent (M ≃ᵢ M)
            (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom))) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  have hEq := compact_restriction_eq_selected_identity_lift
    P n hn hDim hQ hMS D B C hR3 T ρ hJoint hRestrict
  exact congrArg (fun k : Torus r →*
      Component (TwistorHolomorphicAutomorphisms P.tangent D B) =>
      Subgroup.centralizer (Set.range k)) hEq

def complexActionIntoCentralizer : ComplexTorus r →*
    selectedMetricCentralizer P n D B C T
      ρ hJoint hRestrict :=
  intoCompactCentralizer (complexIdentityAutAction P.tangent D B C
    (actionOfEmbedding P.tangent T) ρ hJoint hRestrict)

@[simp] theorem complexActionIntoCentralizer_coe (z : ComplexTorus r) :
    (complexActionIntoCentralizer P n D B C T
      ρ hJoint hRestrict z :
      Component (TwistorHolomorphicAutomorphisms P.tangent D B)) =
      complexIdentityAutAction P.tangent D B C
        (actionOfEmbedding P.tangent T) ρ hJoint hRestrict z := rfl

theorem complexActionIntoCentralizer_continuous :
    Continuous (complexActionIntoCentralizer P n D B C T
      ρ hJoint hRestrict) :=
  intoCompactCentralizer_continuous _
    (complexIdentityAutAction_continuous P.tangent D B C
      (actionOfEmbedding P.tangent T) ρ hJoint hRestrict)

theorem selectedMetricCentralizer_isClosed :
    IsClosed (selectedMetricCentralizer P n D B C T
      ρ hJoint hRestrict :
      Set (Component (TwistorHolomorphicAutomorphisms P.tangent D B))) := by
  letI := B.charts
  letI := B.complexManifold
  letI : T2Space (SphereBundleTotal P.tangent) := inferInstance
  letI : T2Space (TwistorHolomorphicAutomorphisms P.tangent D B) := by
    unfold TwistorHolomorphicAutomorphisms
    infer_instance
  letI : T2Space
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    inferInstance
  exact compactCentralizer_isClosed _

end
end QuaternionicSymmetry.ManifoldTwistorSelectedMetricCentralizer
