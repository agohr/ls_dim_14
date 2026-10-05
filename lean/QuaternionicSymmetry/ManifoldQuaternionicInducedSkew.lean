import QuaternionicSymmetry.ManifoldQuaternionicFourFormGluing
import QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection

/-! Metricity of the induced connection on the quaternionic rank-three span. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicInducedSkew

open QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
  QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
  QuaternionicSymmetry.ManifoldQuaternionicConnection
  VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem synth_eval_inner_all (S : QuaternionicStructure E)
    (a b : Fin 3 → ℝ) (w : E) :
    inner ℝ (synth S a w) (synth S b w) =
      (∑ t : Fin 3, a t * b t) * ‖w‖ ^ 2 := by
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
    ring

omit [FiniteDimensional ℝ E] in
private theorem synth_inner_polarized (S : QuaternionicStructure E)
    (a b : Fin 3 → ℝ) (u v : E) :
    inner ℝ (synth S a u) (synth S b v) +
      inner ℝ (synth S a v) (synth S b u) =
      2 * (∑ t : Fin 3, a t * b t) * inner ℝ u v := by
  have hu := synth_eval_inner_all S a b u
  have hv := synth_eval_inner_all S a b v
  have huv := synth_eval_inner_all S a b (u + v)
  simp only [map_add, inner_add_left, inner_add_right] at huv
  rw [norm_add_sq_real] at huv
  nlinarith

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

/-- The connection induced on the quaternionic rank-three span is skew for
the standard Euclidean dot product. -/
theorem inducedForm_dot_skew (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (a b : Fin 3 → ℝ) :
    (∑ t : Fin 3, (inducedForm Q D p y u a) t * b t) +
      (∑ t : Fin 3, a t * (inducedForm Q D p y u b) t) = 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let w : E := (‖v‖⁻¹ : ℝ) • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
  let S := Q.reduction.Q (achart E p)
  let Γ := D.form p y u
  have ha := congrArg (fun T : E →L[ℝ] E => T w)
    (synth_inducedForm Q D p y u hy a)
  have hb := congrArg (fun T : E →L[ℝ] E => T w)
    (synth_inducedForm Q D p y u hy b)
  change synth S (inducedForm Q D p y u a) w =
    (Γ.comp (synth S a) - (synth S a).comp Γ) w at ha
  change synth S (inducedForm Q D p y u b) w =
    (Γ.comp (synth S b) - (synth S b).comp Γ) w at hb
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply] at ha hb
  have hm := D.metric p y u (synth S a w) (synth S b w) hy
  have hself := D.metric p y u w w hy
  have hpolar := synth_inner_polarized S a b (Γ w) w
  have hdotA := synth_eval_inner S (inducedForm Q D p y u a) b w hw
  have hdotB := synth_eval_inner S a (inducedForm Q D p y u b) w hw
  rw [ha] at hdotA
  rw [hb] at hdotB
  simp only [inner_sub_left, inner_sub_right] at hdotA hdotB
  have hzero : inner ℝ (Γ w) w = 0 := by
    nlinarith [real_inner_comm w (Γ w)]
  rw [hzero, mul_zero] at hpolar
  linarith

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedSkew
