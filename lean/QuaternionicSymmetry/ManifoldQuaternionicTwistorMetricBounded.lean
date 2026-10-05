import QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricBilinear

/-! The explicit connection metric has a bounded unit ball in each genuine
twistor tangent fiber. The argument uses the actual base orthonormal frame
and vertical coefficient norm, not an assumed equivalence of metric norms. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricBounded

open ManifoldQuaternionicTwistorSplitMetric
open ManifoldQuaternionicTwistorMetricBilinear
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

theorem splitMetricCLM_isVonNBounded (z : SphereBundleTotal Q) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace (J (E := E)) z | splitMetricCLM Q D z v v < 1} := by
  let e := connectionTangentEquiv Q D z
  let k := (tangentBundleCore 𝓘(ℝ,E) M).indexAt z.1
  let V := ManifoldTwistorVerticalComplex.verticalSubmodule
    (ManifoldTwistorCoefficientSphere.coefficientSphereHomeomorph.symm z.2)
  let U : E × V →ₗ[ℝ] TangentSpace (J (E := E)) z :=
    e.symm.toLinearMap.comp
      ((Q.frames.fromFrame k z.1).toLinearMap.prodMap (LinearMap.id : V →ₗ[ℝ] V))
  let Uc := U.toContinuousLinearMap
  have hsubset :
      {v : TangentSpace (J (E := E)) z | splitMetricCLM Q D z v v < 1} ⊆
        Uc '' Metric.ball (0 : E × V) 1 := by
    intro v hv
    let w := e v
    have hbase : 0 ≤ Q.tangentMetricForm z.1 w.1 w.1 := by
      by_cases h : w.1 = 0
      · simp [h]
      · exact (Q.tangentMetricForm_pos z.1 w.1 h).le
    have hvert : 0 ≤ w.2.1 ⬝ᵥ w.2.1 :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg (w.2.1 i))
    have hsum : Q.tangentMetricForm z.1 w.1 w.1 + w.2.1 ⬝ᵥ w.2.1 < 1 := hv
    have hbaseLt : Q.tangentMetricForm z.1 w.1 w.1 < 1 := by linarith
    have hvertLt : w.2.1 ⬝ᵥ w.2.1 < 1 := by linarith
    have hframe : ‖Q.frames.toFrame k z.1 w.1‖ < 1 := by
      have hsq : ‖Q.frames.toFrame k z.1 w.1‖ ^ 2 < 1 := by
        simpa only [Q.tangentMetricForm_apply, real_inner_self_eq_norm_sq] using hbaseLt
      have hn := norm_nonneg (Q.frames.toFrame k z.1 w.1)
      nlinarith
    have hverticalNorm : ‖w.2‖ < 1 := by
      change ‖w.2.1‖ < 1
      apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
      intro i
      have hi : w.2.1 i * w.2.1 i ≤ w.2.1 ⬝ᵥ w.2.1 :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg (w.2.1 j)) (Finset.mem_univ i)
      rw [Real.norm_eq_abs]
      exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
    refine ⟨(Q.frames.toFrame k z.1 w.1, w.2), ?_, ?_⟩
    · simp only [Metric.mem_ball, dist_zero_right, Prod.norm_def]
      exact max_lt hframe hverticalNorm
    · change e.symm (Q.frames.fromFrame k z.1 (Q.frames.toFrame k z.1 w.1), w.2) = v
      rw [Q.frames.from_to k z.1 ((tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at z.1)]
      exact e.symm_apply_apply v
  exact ((NormedSpace.isVonNBounded_ball ℝ (E × V) 1).image Uc).subset hsubset

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricBounded
