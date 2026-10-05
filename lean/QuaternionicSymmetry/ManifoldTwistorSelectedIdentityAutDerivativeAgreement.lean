import QuaternionicSymmetry.ManifoldTwistorSelectedIdentityAutCompactAgreement
import QuaternionicSymmetry.SelectedTorusEmbeddedLieAtlas
import QuaternionicSymmetry.ManifoldTwistorFullMetricCoherentLieTarget
import QuaternionicSymmetry.ComplexLieRealCompanion
import QuaternionicSymmetry.ManifoldImmersionSmooth
import QuaternionicSymmetry.SmoothLieHomDerivativeComposition

/-! Differentiate the literal compact agreement inside one actual inherited
identity-component Lie atlas. The chain rule identifies the compact derivative
with the coherent ordinary-metric lift derivative applied to the selected
torus's derivative. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedIdentityAutDerivativeAgreement

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorSelectedIdentityAutCompactAgreement
open ManifoldTwistorComplexIdentityAutAction
open ManifoldTwistorFullMetricCoherentLieTarget
open ManifoldQuaternionicSelectedTorusFullMetric
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open SelectedTorusEmbeddedLieAtlas
open GeneralClosedSubgroupLieSource ComplexLieRealCompanion
open ManifoldImmersionSmooth
open IdentityComponentLie TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
  (hQ : FullMetricSpanPreservation P.tangent)
  (hMS : MyersSteenrodSource.{0,0})
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (B : CompatibleComplexAtlas P.tangent D n)
  (C : HolomorphicContactData P.tangent D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  {r d : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
  (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal P.tangent))
  (hJoint : letI := B.charts
    ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
      𝓘(ℂ, ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal P.tangent => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal P.tangent),
    ρ (compactInclusion r t) z =
      sphereTotalMap P.tangent
        ((actionOfEmbedding P.tangent T).representation t) z)
  (hRealChart : letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    ChartedSpace VR (M ≃ᵢ M))
  (hRealLie : letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
    LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M))
  (hComplexChart : letI := B.charts
    letI := B.complexManifold
    ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B))
  (hComplexLie : letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
    LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent D B))

include hRealLie hComplexLie

theorem selected_compact_derivative_eq_comp
    (g : letI : MetricSpace M := riemannianMetricSpace P.tangent
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
      letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
      letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hRealLie
      letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
        IdentityComponentLie.charts VR (M ≃ᵢ M)
      EmbeddedRealLieAtlas VR (Fin r → Circle) (Component (M ≃ᵢ M))
        (liftToComponent (M ≃ᵢ M)
          (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom d)
    (hSmooth : letI : MetricSpace M := riemannianMetricSpace P.tangent
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
      letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
      letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
        IdentityComponentLie.charts VR (M ≃ᵢ M)
      letI := B.charts
      letI := B.complexManifold
      letI : ChartedSpace VC
        (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
      letI : ChartedSpace VC
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
        ComplexIdentityComponentLie.charts VC
          (TwistorHolomorphicAutomorphisms P.tangent D B)
      ContMDiff 𝓘(ℝ,VR) 𝓘(ℝ,VC) ∞
        (fullMetricIdentityLift P n hn hDim hQ hMS D B C.line hR3)) :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
    letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hRealLie
    letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
      IdentityComponentLie.charts VR (M ≃ᵢ M)
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
    letI : ChartedSpace VC
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
      ComplexIdentityComponentLie.charts VC
        (TwistorHolomorphicAutomorphisms P.tangent D B)
    letI := g.charts
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC)
      ((complexIdentityAutAction P.tangent D B C
        (actionOfEmbedding P.tangent T) ρ hJoint hRestrict).comp
        (compactInclusion r)) 1 =
      (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC)
        (fullMetricIdentityLift P n hn hDim hQ hMS D B C.line hR3) 1).comp
        (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR)
          ((liftToComponent (M ≃ᵢ M)
            (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom) 1) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
  letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hRealLie
  letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.charts VR (M ≃ᵢ M)
  letI : IsManifold 𝓘(ℝ,VR) ∞ (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.manifold VR (M ≃ᵢ M)
  letI := B.charts
  letI := B.complexManifold
  letI : ChartedSpace VC
    (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
  letI : LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexLie
  letI : ChartedSpace VC
    (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
      ComplexIdentityComponentLie.charts VC
        (TwistorHolomorphicAutomorphisms P.tangent D B)
  letI : IsManifold 𝓘(ℂ,VC) ∞
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.manifold VC _
  letI : IsManifold 𝓘(ℝ,VC) ∞
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexLieRealCompanion.realManifold
  letI := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  have hEq := compact_restriction_eq_selected_identity_lift
    P n hn hDim hQ hMS D B C hR3 T ρ hJoint hRestrict
  have hDerivEq :
      mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC)
          ((complexIdentityAutAction P.tangent D B C
            (actionOfEmbedding P.tangent T) ρ hJoint hRestrict).comp
            (compactInclusion r)) 1 =
        mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC)
          ((fullMetricIdentityLift P n hn hDim hQ hMS D B C.line hR3).comp
            ((liftToComponent (M ≃ᵢ M)
              (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom)) 1 := by
    rw [hEq]
  have hmapSmooth : ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR) ∞
      ((liftToComponent (M ≃ᵢ M)
        (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom) :=
    ManifoldImmersionSmooth.smoothEmbedding_contMDiff g.smoothEmbedding
  exact hDerivEq.trans (SmoothLieHomDerivativeComposition.mfderiv_comp_hom_one
    (fullMetricIdentityLift P n hn hDim hQ hMS D B C.line hR3)
    ((liftToComponent (M ≃ᵢ M)
      (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom)
    hSmooth hmapSmooth)

end
end QuaternionicSymmetry.ManifoldTwistorSelectedIdentityAutDerivativeAgreement
