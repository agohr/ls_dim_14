import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaTorsion
import QuaternionicSymmetry.GeneralLeviCivitaAdaptedMetricBridge

/-! A metric-matched ordinary LC form becomes skew-adjoint in the
genuine orthonormal tangent gauge. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaMetric

open Filter Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicAdaptedLeviCivitaSolder
open GeneralLeviCivitaAdaptedMetricBridge
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
    (TangentSpace 𝓘(ℝ,E) : M → Type _))
  (D : CoordinateLeviCivitaConnection g)

theorem adaptedLeviCivitaForm_metric
    (hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,E) x),
      g.inner x v w = Q.tangentMetricForm x v w)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u a b : E) :
    inner ℝ (adaptedLeviCivitaForm Q g D p y u a) b +
      inner ℝ a (adaptedLeviCivitaForm Q g D p y u b) = 0 := by
  let inv := coordinateInverse Q p y
  let v := inv a
  let w := inv b
  have hright := coordinateInverse_right Q p y hy
  have hva : solder Q p y v = a := by
    have h := congrArg (fun T : E →L[ℝ] E => T a) hright
    simpa only [v, inv, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply] using h
  have hwb : solder Q p y w = b := by
    have h := congrArg (fun T : E →L[ℝ] E => T b) hright
    simpa only [w, inv, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply] using h
  have heq : (fun z => chartMetric g p z v w) =ᶠ[𝓝 y]
      fun z => coordinateMetric Q p z v w := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact chartMetric_eq_coordinateMetric Q g hmetric p z hz v w
  have hder := heq.fderiv_eq (𝕜 := ℝ)
  have hm := D.metric p y u v w hy
  rw [hder,
    chartMetric_eq_coordinateMetric Q g hmetric p y hy (D.form p y u v) w,
    chartMetric_eq_coordinateMetric Q g hmetric p y hy v (D.form p y u w)] at hm
  have hcoordinate := coordinateMetric_fderiv Q p y hy u v w
  rw [hcoordinate] at hm
  simp only [coordinateMetric, hva, hwb] at hm
  have hAv := adaptedLeviCivitaForm_apply_solder Q g D p y hy u v
  have hAw := adaptedLeviCivitaForm_apply_solder Q g D p y hy u w
  rw [hva] at hAv
  rw [hwb] at hAw
  rw [hAv, hAw]
  simp only [inner_sub_left, inner_sub_right]
  linarith

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaMetric
