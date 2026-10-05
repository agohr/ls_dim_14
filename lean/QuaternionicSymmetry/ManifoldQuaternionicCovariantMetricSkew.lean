import QuaternionicSymmetry.ManifoldQuaternionicCoordinateMetricField
import QuaternionicSymmetry.LocalConnectionCovariantMetricSkew
import QuaternionicSymmetry.ManifoldQuaternionicMetricCurvature

/-! The covariant derivative of the actual tangent curvature remains skew
for the actual chart metric. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCovariantMetricSkew
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicMetricCurvature
open QuaternionicSymmetry.LocalConnection
open QuaternionicSymmetry.LocalConnectionGauge
open QuaternionicSymmetry.LocalConnectionBianchi
open QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
open QuaternionicSymmetry.LocalConnectionCovariantMetricSkew
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinate_curvature_gauge (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E) :
    curvature (coordinateConnection Q D p) y u v =
      coordinateInverse Q p y * D.curvature Q p y u v * solder Q p y := by
  have hΓ : DifferentiableAt ℝ (D.form p) y :=
    ((D.smooth_form p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  have hg := ManifoldQuaternionicCoordinateSecondBianchi.solder_contDiffAt Q p y hy
  have hh := ManifoldQuaternionicCoordinateSecondBianchi.coordinateInverse_contDiffAt Q p y hy
  have hleft : (fun z => coordinateInverse Q p z * solder Q p z) =ᶠ[𝓝 y]
      fun _ => 1 := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact coordinateInverse_left Q p z hz
  exact curvature_transform (D.form p) (solder Q p) (coordinateInverse Q p)
    y hΓ (hg.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num))
      (hh.differentiableAt (by norm_num)) hleft
        (coordinateInverse_right Q p y hy) u v

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinate_curvature_metric_skew (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w z : E) :
    coordinateMetricField Q p y
        (curvature (coordinateConnection Q D p) y u v w) z +
      coordinateMetricField Q p y w
        (curvature (coordinateConnection Q D p) y u v z) = 0 := by
  rw [coordinateMetricField_apply Q p y hy,
    coordinateMetricField_apply Q p y hy,
    coordinateMetric, coordinateMetric]
  rw [coordinate_curvature_gauge Q D p y hy]
  simp only [ContinuousLinearMap.mul_apply]
  have hs := coordinateInverse_right Q p y hy
  have hsw (a : E) : solder Q p y (coordinateInverse Q p y a) = a :=
    congrArg (fun F : E →L[ℝ] E => F a) hs
  simp only [hsw]
  exact tangentCurvature_skew Q D p y u v (solder Q p y w) (solder Q p y z) hy

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem curvature_differentiableAt (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E) :
    DifferentiableAt ℝ (fun z => curvature (coordinateConnection Q D p) z u v) y := by
  let Γ := coordinateConnection Q D p
  have hΓ : ContDiffAt ℝ 2 Γ y :=
    ManifoldQuaternionicCoordinateSecondBianchi.coordinateConnection_contDiffAt Q D p y hy
  have h₁ : DifferentiableAt ℝ Γ y := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) y :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have huv : DifferentiableAt ℝ (fun z => fderiv ℝ Γ z u v) y :=
    (h₂.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hvu : DifferentiableAt ℝ (fun z => fderiv ℝ Γ z v u) y :=
    (h₂.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hu : DifferentiableAt ℝ (fun z => Γ z u) y :=
    h₁.clm_apply (differentiableAt_const _)
  have hv : DifferentiableAt ℝ (fun z => Γ z v) y :=
    h₁.clm_apply (differentiableAt_const _)
  simpa only [curvature_apply] using
    ((huv.sub hvu).add ((hu.hasFDerivAt.mul' hv.hasFDerivAt).differentiableAt)).sub
      ((hv.hasFDerivAt.mul' hu.hasFDerivAt).differentiableAt)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinate_covariantCurvature_metric_skew (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a u v w z : E) :
    coordinateMetricField Q p y
        (covariantCurvatureDerivative (coordinateConnection Q D p) y a u v w) z +
      coordinateMetricField Q p y w
        (covariantCurvatureDerivative (coordinateConnection Q D p) y a u v z) = 0 := by
  apply covariantCurvatureDerivative_metric_skew
    (coordinateConnection Q D p) (coordinateMetricField Q p) y a u v w z
    (coordinateMetricField_differentiableAt Q p y hy)
    (curvature_differentiableAt Q D p y hy u v)
  · intro b c
    rw [coordinateMetricField_fderiv Q D p y hy a b c]
    rw [coordinateMetricField_apply Q p y hy,
      coordinateMetricField_apply Q p y hy]
  · intro b c
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact coordinate_curvature_metric_skew Q D p z hz u v b c

end
end QuaternionicSymmetry.ManifoldQuaternionicCovariantMetricSkew
