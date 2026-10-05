import QuaternionicSymmetry.ManifoldQuaternionicHomothetyCurvature

/-! Ricci and scalar curvature of the actual rescaled metric. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyScalar
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicHomothetyReduction ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyCurvature
open scoped Manifold ContDiff
noncomputable section
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := I) (M := M) (n := n))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

omit [I.Boundaryless] in
theorem localRicci_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (hy : y ∈ (extChartAt I p).target) (v w : E) :
    localRicci (rescaleMetric Q s hs) (rescaleConnection Q D s hs) p y hy v w =
      s⁻¹ ^ 2 * localRicci Q D p y hy v w := by
  simp only [localRicci, adaptedCurvature_rescale, real_inner_smul_left,
    ← Finset.mul_sum]

omit [I.Boundaryless] in
theorem localScalarCurvature_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (hy : y ∈ (extChartAt I p).target) :
    localScalarCurvature (rescaleMetric Q s hs) (rescaleConnection Q D s hs) p y hy =
      s⁻¹ ^ 2 * localScalarCurvature Q D p y hy := by
  simp only [localScalarCurvature, localRicci_rescale, ← Finset.mul_sum]

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyScalar
