import QuaternionicSymmetry.ManifoldQuaternionicChartProjection

/-! The inverse actual tangent-gauge conjugation identifies the moving
chartwise Q-plane with the fixed adapted quaternionic span. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicChartPlaneDeconjugation

open ManifoldQuaternionicReduction
open ManifoldQuaternionicChartProjection
open VectorBundleFrameTransitions
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem inverseChartConjugation_mem_quaternionicSpan
    (i : atlas E M) (x : M)
    (hx : x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet i)
    (T : E →L[ℝ] E) (hT : T ∈ Q.chartSpan i x) :
    inverseChartConjugation Q i x T ∈
      quaternionicSpan (Q.reduction.Q i) := by
  rw [Q.chartSpan_eq_map] at hT
  obtain ⟨U, hU, rfl⟩ := hT
  have hto : Q.frames.toFrame i x * Q.frames.fromFrame i x = 1 := by
    ext v
    exact Q.frames.to_from i x hx v
  rw [inverseChartConjugation_apply]
  change Q.frames.toFrame i x *
      (Q.frames.fromFrame i x * U * Q.frames.toFrame i x) *
      Q.frames.fromFrame i x ∈ quaternionicSpan (Q.reduction.Q i)
  convert hU using 1
  simp only [mul_assoc, ← mul_assoc (Q.frames.toFrame i x)
    (Q.frames.fromFrame i x), hto, one_mul, mul_one]

end
end QuaternionicSymmetry.ManifoldQuaternionicChartPlaneDeconjugation
