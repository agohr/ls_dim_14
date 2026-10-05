import QuaternionicSymmetry.ManifoldTwistorSelectedComplexCompactAgreement

/-! The genuine complex contact-torus action commutes with the selected
maximal compact metric-isometry torus inside the actual full twistor
automorphism group. This group-level fact requires no Lie derivative. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedComplexCentralizer

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullAutomorphismIdentityComponent
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorSelectedComplexCompactAgreement
open ManifoldTwistorComplexFullAutAction
open ManifoldQuaternionicSelectedTorusFullMetric
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open IdentityComponentLie TorusLaurentRepresentation
open ComplexTorusHolomorphicStructure
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

theorem commutes_with_selected_metric_torus
    (z : ComplexTorus r) (t : Torus r) :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    (complexFullAutAction P.tangent D B C (actionOfEmbedding P.tangent T)
      ρ hJoint hRestrict z) *
      ((fullMetricIdentityLift P n hn hDim hQ hMS D B C.line hR3)
        ((liftToComponent (M ≃ᵢ M)
          (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom t)).1 =
      ((fullMetricIdentityLift P n hn hDim hQ hMS D B C.line hR3)
        ((liftToComponent (M ≃ᵢ M)
          (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom t)).1 *
        complexFullAutAction P.tangent D B C (actionOfEmbedding P.tangent T)
          ρ hJoint hRestrict z := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  rw [← compact_agreement P n hn hDim hQ hMS D B C hR3 T ρ hJoint hRestrict t]
  change (complexFullAutAction P.tangent D B C (actionOfEmbedding P.tangent T)
      ρ hJoint hRestrict) z *
      (complexFullAutAction P.tangent D B C (actionOfEmbedding P.tangent T)
        ρ hJoint hRestrict) (compactInclusion r t) = _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (mul_comm z (compactInclusion r t))

end
end QuaternionicSymmetry.ManifoldTwistorSelectedComplexCentralizer
