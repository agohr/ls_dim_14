import QuaternionicSymmetry.ManifoldQuaternionicTangentSynthMetric
import QuaternionicSymmetry.ManifoldQuaternionicLocalGaugeTransport

/-! Quaternionic coefficient orthogonality in one fixed adapted chart. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicLocalSynthMetric
open ManifoldQuaternionicMetric
open ManifoldQuaternionicLocalGaugeTransport
open ManifoldQuaternionicTangentSynthMetric
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Matrix
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem localTangentSynth_chartMetric (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a b : Fin 3 → ℝ) (v : E) :
    Q.chartMetricForm i x (localTangentSynth Q i x a v)
        (localTangentSynth Q i x b v) =
      (a ⬝ᵥ b) * Q.chartMetricForm i x v v := by
  let T := Q.frames.toFrame i x
  let F := Q.frames.fromFrame i x
  change inner ℝ (T (F (synth (Q.reduction.Q i) a (T v))))
      (T (F (synth (Q.reduction.Q i) b (T v)))) =
    (a ⬝ᵥ b) * inner ℝ (T v) (T v)
  rw [Q.frames.to_from i x hi, Q.frames.to_from i x hi]
  simpa only [real_inner_self_eq_norm_sq] using
    synth_eval_inner_all (Q.reduction.Q i) a b (T v)

theorem chartMetricForm_pos (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (v : E) (hv : v ≠ 0) :
    0 < Q.chartMetricForm i x v v := by
  rw [Q.chartMetricForm_apply]
  apply real_inner_self_pos.mpr
  intro h
  apply hv
  have hh := congrArg (Q.frames.fromFrame i x) h
  simpa only [map_zero, Q.frames.from_to i x hi] using hh

end
end QuaternionicSymmetry.ManifoldQuaternionicLocalSynthMetric
