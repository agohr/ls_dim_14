import QuaternionicSymmetry.ManifoldQuaternionicHomothetyReduction

/-! The actual tangent metric scales quadratically under a constant frame homothety. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyMetric
open ManifoldQuaternionicMetric ManifoldQuaternionicHomothetyReduction
open scoped Manifold ContDiff
noncomputable section
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
variable (Q : SmoothQuaternionicHermitianTangent (I := I) (M := M) (n := n))

theorem tangentMetricForm_rescale (s : ℝ) (hs : s ≠ 0)
    (x : M) (v w : TangentSpace I x) :
    (rescaleMetric Q s hs).tangentMetricForm x v w =
      s ^ 2 * Q.tangentMetricForm x v w := by
  rw [SmoothQuaternionicHermitianTangent.tangentMetricForm_apply,
    SmoothQuaternionicHermitianTangent.tangentMetricForm_apply]
  change inner ℝ (s • Q.frames.toFrame ((tangentBundleCore I M).indexAt x) x v)
    (s • Q.frames.toFrame ((tangentBundleCore I M).indexAt x) x w) = _
  simp [real_inner_smul_left, real_inner_smul_right, pow_two, mul_assoc]

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyMetric
