import QuaternionicSymmetry.ManifoldQuaternionicHomothetyConnection
import QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature

/-! Constant metric homothety leaves the connection curvature unchanged and
scales adapted curvature by the inverse square of the frame scale. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyCurvature
open ManifoldQuaternionicConnection ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicHomothetyReduction ManifoldQuaternionicHomothetyConnection
open scoped Manifold ContDiff
noncomputable section
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := I) (M := M) (n := n))
  (D : CompatibleTangentConnection Q)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem unsolder_rescale (s : ℝ) (hs : s ≠ 0) (p : M) (y : E)
    (hy : y ∈ (extChartAt I p).target) :
    unsolder (rescaleMetric Q s hs) p y = s⁻¹ • unsolder Q p y := by
  rw [unsolder_eq_fromFrame (rescaleMetric Q s hs) p y hy,
    unsolder_eq_fromFrame Q p y hy]
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem adaptedCurvature_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (hy : y ∈ (extChartAt I p).target)
    (u v w : E) :
    adaptedCurvature (rescaleMetric Q s hs) (rescaleConnection Q D s hs)
      p y hy u v w = s⁻¹ ^ 2 • adaptedCurvature Q D p y hy u v w := by
  have hu := congrArg (fun L : E →L[ℝ] E => L u)
    (unsolder_rescale Q s hs p y hy)
  have hv := congrArg (fun L : E →L[ℝ] E => L v)
    (unsolder_rescale Q s hs p y hy)
  simp only [ContinuousLinearMap.smul_apply] at hu hv
  change LocalConnection.curvature (D.form p) y
    (unsolder (rescaleMetric Q s hs) p y u)
    (unsolder (rescaleMetric Q s hs) p y v) w = _
  rw [hu, hv]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, pow_two]
  rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyCurvature
