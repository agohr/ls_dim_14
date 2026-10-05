import QuaternionicSymmetry.ManifoldQuaternionicInducedCoefficientMap
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal

/-! Metric extraction of quaternionic coefficients from one nonzero tangent
vector. This works for a rectangular submanifold derivative; no ambient
inverse derivative is used. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicTangentSynthMetric
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicRankThreeOrthogonal
open ManifoldQuaternionicMetric
open ManifoldTwistorSphereBundle
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Matrix
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem synth_eval_inner_all (S : QuaternionicStructure E)
    (a b : Fin 3 → ℝ) (w : E) :
    inner ℝ (synth S a w) (synth S b w) =
      (a ⬝ᵥ b) * ‖w‖ ^ 2 := by
  by_cases hw : w = 0
  · subst w
    simp
  · let z : E := (‖w‖⁻¹ : ℝ) • w
    have hz : ‖z‖ = 1 := norm_smul_inv_norm hw
    have h := synth_eval_inner S a b z hz
    have hrep : w = ‖w‖ • z := by
      rw [show z = (‖w‖⁻¹ : ℝ) • w from rfl, smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]
    conv_lhs => rw [hrep]
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    rw [h]
    simp only [dotProduct]
    ring

theorem tangentSynth_metric (x : M) (a b : Fin 3 → ℝ)
    (v : TangentSpace 𝓘(ℝ,E) x) :
    Q.tangentMetricForm x (tangentSynth Q x a v) (tangentSynth Q x b v) =
      (a ⬝ᵥ b) * Q.tangentMetricForm x v v := by
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  let T := Q.frames.toFrame i x
  let F := Q.frames.fromFrame i x
  have hi := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x
  change inner ℝ (T (F (synth (Q.reduction.Q i) a (T v))))
      (T (F (synth (Q.reduction.Q i) b (T v)))) =
    (a ⬝ᵥ b) * inner ℝ (T v) (T v)
  rw [Q.frames.to_from i x hi, Q.frames.to_from i x hi]
  simpa only [real_inner_self_eq_norm_sq] using
    synth_eval_inner_all (Q.reduction.Q i) a b (T v)

end
end QuaternionicSymmetry.ManifoldQuaternionicTangentSynthMetric
