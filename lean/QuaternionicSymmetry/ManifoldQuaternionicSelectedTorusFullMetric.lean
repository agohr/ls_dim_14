import QuaternionicSymmetry.ManifoldFullMetricMaximalTorusComplexifiedLie
import QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput
import QuaternionicSymmetry.CompactLieTorusEquivTransfer

/-! Preserve the *same* selected quaternionic-isometry torus when moving
to ordinary full metric isometries, the compact group named in BWW 6.5. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicSelectedTorusFullMetric

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldQuaternionicFullIsometryEmbedding
open CompactLieTorusInputs CompactLieTorusEquivTransfer
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

def selectedFullMetricTorus {r : ℕ}
    (T : TorusEmbedding (QuaternionicIsometries P.tangent) r) :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    TorusEmbedding (M ≃ᵢ M) r := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  exact transport (fullMetricIsometryEquiv P n hn hDim hQ hMS)
    (toFullMetricIsometry_continuous P.tangent) T

theorem selectedFullMetricTorus_maximal {r : ℕ}
    (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent)) :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    (selectedFullMetricTorus P n hn hDim hQ hMS T).IsMaximal (M ≃ᵢ M) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  exact transport_maximal (fullMetricIsometryEquiv P n hn hDim hQ hMS)
    (toFullMetricIsometry_continuous P.tangent)
    (fullMetricIsometryEquiv_symm_continuous P n hn hDim hQ hMS) T hMax

end
end QuaternionicSymmetry.ManifoldQuaternionicSelectedTorusFullMetric
