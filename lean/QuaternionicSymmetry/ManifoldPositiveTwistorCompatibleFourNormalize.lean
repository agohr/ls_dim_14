import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourHomothety

/-! Scalar-48 normalization of the actual four-dimensional compatible
Einstein geometry, conditional on an explicitly supplied positive *global*
scalar constant. Establishing such a constant by a four-dimensional
contracted-Bianchi/Schur argument is separate from this scaling theorem. -/

namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourNormalize

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveTwistorCompatibleFourHomothety
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyScalar
open ManifoldQuaternionicScalarCurvature
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- A positive global scalar constant `c` is normalized to 48 by scaling
adapted frames by `sqrt(c/48)` (so the tangent metric scales by `c/48`). -/
def scaleTo48 (c : ℝ) : ℝ := Real.sqrt (c / 48)

theorem scaleTo48_pos {c : ℝ} (hc : 0 < c) : 0 < scaleTo48 c := by
  exact Real.sqrt_pos.2 (div_pos hc (by norm_num))

theorem scaleTo48_sq {c : ℝ} (hc : 0 < c) : (scaleTo48 c) ^ 2 = c / 48 := by
  exact Real.sq_sqrt (le_of_lt (div_pos hc (by norm_num)))

theorem inverse_scaleTo48_sq_mul {c : ℝ} (hc : 0 < c) :
    (scaleTo48 c)⁻¹ ^ 2 * c = 48 := by
  rw [inv_pow, scaleTo48_sq hc]
  have hc0 : c ≠ 0 := ne_of_gt hc
  field_simp

/-- The rescaled genuine four-dimensional geometry has scalar 48 whenever
the original scalar is the supplied positive global constant. -/
theorem scalar_48_of_global_constant
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (c : ℝ) (hc : 0 < c)
    (hconstant : ∀ (p : M) (y : E)
      (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy = c)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    localScalarCurvature
      (rescaleFour P (scaleTo48 c) (scaleTo48_pos hc)).tangent
      (rescaleFour P (scaleTo48 c) (scaleTo48_pos hc)).connection
      p y hy = 48 := by
  change localScalarCurvature
    (rescaleMetric P.tangent (scaleTo48 c) (ne_of_gt (scaleTo48_pos hc)))
    (rescaleConnection P.tangent P.connection (scaleTo48 c)
      (ne_of_gt (scaleTo48_pos hc))) p y hy = 48
  rw [localScalarCurvature_rescale, hconstant p y hy]
  exact inverse_scaleTo48_sq_mul hc

/-- Compactness and connectedness remain part of the normalized four-
dimensional geometry; no higher-dimensional scalar theorem is invoked. -/
theorem compact_scalar_48_of_global_constant
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry
      (E := E) (M := M))
    (c : ℝ) (hc : 0 < c)
    (hconstant : ∀ (p : M) (y : E)
      (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy = c)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    localScalarCurvature
      (rescaleCompactFour P (scaleTo48 c) (scaleTo48_pos hc)).tangent
      (rescaleCompactFour P (scaleTo48 c) (scaleTo48_pos hc)).connection
      p y hy = 48 := by
  exact scalar_48_of_global_constant
    P.toPositiveTwistorCompatibleFourGeometry c hc hconstant p y hy

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourNormalize
