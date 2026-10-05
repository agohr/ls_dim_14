import QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutAction
import QuaternionicSymmetry.ManifoldTwistorSelectedMetricLiftHomAgreement

/-! The same selected compact torus agrees as a homomorphism valued in the
actual identity component of twistor holomorphic automorphisms. This is the
group-level equality whose derivative can be taken in one inherited atlas. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedIdentityAutCompactAgreement

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorSelectedMetricLiftHomAgreement
open ManifoldTwistorComplexIdentityAutAction
open ManifoldQuaternionicSelectedTorusFullMetric
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
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

theorem compact_restriction_eq_selected_identity_lift :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    (complexIdentityAutAction P.tangent D B C
      (actionOfEmbedding P.tangent T) ρ hJoint hRestrict).comp
        (compactInclusion r) =
      (fullMetricIdentityLift P n hn hDim hQ hMS D B C.line hR3).comp
        ((liftToComponent (M ≃ᵢ M)
          (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  apply MonoidHom.ext
  intro t
  apply Subtype.ext
  have h := congrArg (fun f : Torus r →* TwistorHolomorphicAutomorphisms P.tangent D B => f t)
    (compact_restriction_eq_selected_metric_lift P n hn hDim hQ hMS D B C hR3 T
      ρ hJoint hRestrict)
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply,
    complexIdentityAutAction_coe] using h

end
end QuaternionicSymmetry.ManifoldTwistorSelectedIdentityAutCompactAgreement
