import QuaternionicSymmetry.ManifoldQuaternionicCoordinateSecondBianchi
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The actual tangent metric and its coordinate connection. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open QuaternionicSymmetry.LocalConnectionBianchi
open QuaternionicSymmetry.LocalConnectionGauge
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- Coordinate metric determined by the genuine adapted tangent frame. -/
def coordinateMetric (p : M) (y : E) (v w : E) : ℝ :=
  inner ℝ (solder Q p y v) (solder Q p y w)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateMetric_fderiv (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w : E) :
    fderiv ℝ (fun z => coordinateMetric Q p z v w) y u =
      inner ℝ (fderiv ℝ (solder Q p) y u v) (solder Q p y w) +
        inner ℝ (solder Q p y v) (fderiv ℝ (solder Q p) y u w) := by
  have hs : DifferentiableAt ℝ (solder Q p) y :=
    (ManifoldQuaternionicCoordinateSecondBianchi.solder_contDiffAt Q p y hy).differentiableAt
      (by norm_num)
  have hv : DifferentiableAt ℝ (fun z => solder Q p z v) y :=
    hs.clm_apply (differentiableAt_const _)
  have hw : DifferentiableAt ℝ (fun z => solder Q p z w) y :=
    hs.clm_apply (differentiableAt_const _)
  change fderiv ℝ (fun z => inner ℝ (solder Q p z v) (solder Q p z w)) y u = _
  rw [fderiv_inner_apply ℝ hv hw u]
  rw [fderiv_eval_const hs v u, fderiv_eval_const hs w u]
  exact add_comm _ _

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Metric compatibility, derived from the adapted-frame skewness field and
the actual solder gauge transformation. -/
theorem coordinateConnection_metric (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w : E) :
    fderiv ℝ (fun z => coordinateMetric Q p z v w) y u =
      coordinateMetric Q p y (coordinateConnection Q D p y u v) w +
        coordinateMetric Q p y v (coordinateConnection Q D p y u w) := by
  have hright := coordinateInverse_right Q p y hy
  have hs (a : E) : solder Q p y (coordinateInverse Q p y a) = a := by
    exact congrArg (fun F : E →L[ℝ] E => F a) hright
  rw [coordinateMetric_fderiv Q p y hy u v w]
  simp only [coordinateMetric, coordinateConnection, transform_apply,
    ContinuousLinearMap.mul_apply, hs]
  have hm := D.metric p y u (solder Q p y v) (solder Q p y w) hy
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
    inner_add_left, inner_add_right]
  linarith

end
end QuaternionicSymmetry.ManifoldQuaternionicCoordinateMetricity
