import QuaternionicSymmetry.ManifoldTwistorFullMetricIsometryComparison
import QuaternionicSymmetry.ComplexIdentityComponentLie

/-! BWW 6.5 concerns the ordinary metric-isometry group. This target is
worded on that group. Its quaternionic-isometry counterpart is a theorem,
transported through BG-Q1 and Myers–Steenrod, not part of the source. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullMetricUniversalTarget

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorFullAutUniversalComplexificationTarget
open CompactRealFormUniversalComplexification
open UniversalComplexificationEquivTransfer
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

/-- Genuine universal group-level target on ordinary metric isometries.
BG-Q1 and Myers–Steenrod are present because their checked comparison
constructs the actual ordinary-isometry lift used in this formulation. -/
def FullMetricUniversalConclusion : Prop :=
  letI := B.charts
  letI := B.complexManifold
  letI : MetricSpace M :=
    ManifoldQuaternionicRiemannianDistance.riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) :=
    MetricIsometryCompactness.isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) :=
    MetricIsometryCompactness.isometryEquiv_topologicalGroup (X := M)
  ∃ (V : Type) (hNorm : NormedAddCommGroup V),
    letI : NormedAddCommGroup V := hNorm
    ∃ (hSpace : NormedSpace ℂ V),
      letI : NormedSpace ℂ V := hSpace
      ∃ (hFinite : FiniteDimensional ℂ V)
        (hChart : ChartedSpace V (TwistorHolomorphicAutomorphisms P.tangent D B)),
        letI : FiniteDimensional ℂ V := hFinite
        letI : ChartedSpace V (TwistorHolomorphicAutomorphisms P.tangent D B) := hChart
        IsManifold 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms P.tangent D B) ∧
        ∃ hLie : LieGroup 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms P.tangent D B),
          letI : LieGroup 𝓘(ℂ,V) ∞
              (TwistorHolomorphicAutomorphisms P.tangent D B) := hLie
          letI : ChartedSpace V
              (IdentityComponentLie.Component
                (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
            ComplexIdentityComponentLie.charts V
              (TwistorHolomorphicAutomorphisms P.tangent D B)
          letI : LieGroup 𝓘(ℂ,V) ∞
              (IdentityComponentLie.Component
                (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
            ComplexIdentityComponentLie.lieGroup V
              (TwistorHolomorphicAutomorphisms P.tangent D B)
          IsUniversalComplexification (VC := V)
            (fullMetricIdentityLift P n hn hDim hQ hMS D B L hR3)

theorem quaternionic_of_fullMetric
    (h : FullMetricUniversalConclusion P n hn hDim hQ hMS D B L hR3) :
    FullAutUniversalComplexificationConclusion P.tangent D B L hR3 := by
  letI := B.charts
  letI := B.complexManifold
  letI : MetricSpace M :=
    ManifoldQuaternionicRiemannianDistance.riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) :=
    MetricIsometryCompactness.isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) :=
    MetricIsometryCompactness.isometryEquiv_topologicalGroup (X := M)
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hUniversal⟩ := h
  refine ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,?_⟩
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V (TwistorHolomorphicAutomorphisms P.tangent D B) := hChart
  letI : LieGroup 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms P.tangent D B) := hLie
  letI : ChartedSpace V
      (IdentityComponentLie.Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.charts V
      (TwistorHolomorphicAutomorphisms P.tangent D B)
  letI : LieGroup 𝓘(ℂ,V) ∞
      (IdentityComponentLie.Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.lieGroup V
      (TwistorHolomorphicAutomorphisms P.tangent D B)
  have hTransport := precomp
    (fullMetricIdentityLift P n hn hDim hQ hMS D B L hR3)
    (identityComponentEquiv P n hn hDim hQ hMS)
    (identityComponentEquiv_continuous P n hn hDim hQ hMS)
    (identityComponentEquiv_symm_continuous P n hn hDim hQ hMS)
    hUniversal
  rw [fullMetricIdentityLift_comp_equiv] at hTransport
  exact hTransport

end
end QuaternionicSymmetry.ManifoldTwistorFullMetricUniversalTarget
