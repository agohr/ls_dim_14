import QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
import Mathlib.LinearAlgebra.Basis.Basic

/-! Orthogonality of the quaternionic three-plane transitions obtained from
the actual metric tangent frame changes. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal

open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

omit [FiniteDimensional ℝ E] in
theorem synth_basis (S : QuaternionicStructure E) (t : Fin 3) :
    synth S (Pi.basisFun ℝ (Fin 3) t) = quaternionicGenerator S t := by
  change ((quaternionicSpan S).subtype
    ((spanBasis S).equivFun.symm (Pi.basisFun ℝ (Fin 3) t))) = _
  rw [Pi.basisFun_apply, Basis.equivFun_symm_single]
  exact Module.Basis.span_apply (quaternionicGenerator_linearIndependent S) t

omit [FiniteDimensional ℝ E] in
theorem synth_apply (S : QuaternionicStructure E) (a : Fin 3 → ℝ) :
    synth S a = ∑ t : Fin 3, a t • quaternionicGenerator S t := by
  calc
    synth S a = synth S (∑ t : Fin 3, a t • Pi.basisFun ℝ (Fin 3) t) := by
      congr 1
      simpa [Pi.basisFun_repr] using (Pi.basisFun ℝ (Fin 3)).sum_repr a |>.symm
    _ = ∑ t : Fin 3, a t • quaternionicGenerator S t := by
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      simpa only [Pi.basisFun_apply] using synth_basis S t

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem generator_apply_eq_frame (S : QuaternionicStructure E)
    (w : E) (t : Fin 3) :
    quaternionicGenerator S t w = S.frame w (Fin.succ t) := by
  fin_cases t <;> rfl

omit [FiniteDimensional ℝ E] in
theorem synth_eval (S : QuaternionicStructure E) (a : Fin 3 → ℝ) (w : E) :
    synth S a w = ∑ t : Fin 3, a t • S.frame w (Fin.succ t) := by
  rw [synth_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  congr 1
  funext t
  rw [generator_apply_eq_frame]

omit [FiniteDimensional ℝ E] in
theorem synth_eval_inner (S : QuaternionicStructure E)
    (a b : Fin 3 → ℝ) (w : E) (hw : ‖w‖ = 1) :
    inner ℝ (synth S a w) (synth S b w) =
      ∑ t : Fin 3, a t * b t := by
  rw [synth_eval, synth_eval]
  have horth : Orthonormal ℝ (fun t : Fin 3 => S.frame w (Fin.succ t)) :=
    (S.frame_orthonormal w hw).comp Fin.succ (Fin.succ_injective 3)
  simpa using
    horth.inner_sum a b Finset.univ

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := I) (M := M) (n := n))

theorem synth_rankThreeCoordChange (i j : atlas H M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) (a : Fin 3 → ℝ) :
    synth (Q.reduction.Q j) (Q.reduction.rankThreeCoordChange i j x a) =
      (transitionAtlas Q.frames.adaptedCore).adjointCoordChange i j x
        (synth (Q.reduction.Q i) a) := by
  rw [QuaternionicFrameReduction.rankThreeCoordChange_apply]
  apply synth_coeff_of_mem
  apply Q.reduction.map_span_le i j x hi hj
  exact ⟨_, synth_mem _ a, rfl⟩

theorem synth_rankThreeCoordChange_eval (i j : atlas H M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) (a : Fin 3 → ℝ) (v : E) :
    synth (Q.reduction.Q j) (Q.reduction.rankThreeCoordChange i j x a)
      (Q.frames.coordChange i j x v) =
      Q.frames.coordChange i j x (synth (Q.reduction.Q i) a v) := by
  rw [synth_rankThreeCoordChange Q i j x hi hj a]
  rw [adjointCoordChange_apply]
  change Q.frames.coordChange i j x
      (synth (Q.reduction.Q i) a
        (Q.frames.coordChange j i x (Q.frames.coordChange i j x v))) = _
  have hinv : Q.frames.coordChange j i x (Q.frames.coordChange i j x v) = v := by
    rw [Q.frames.coordChange_comp i j i x hi hj hi,
      Q.frames.coordChange_self i x hi]
  rw [hinv]

/-- The rank-three transition is orthogonal for the standard coefficient
dot product. This follows from the metric transition of the actual tangent
bundle and the quaternionic orthonormal frame at a unit vector. -/
theorem rankThreeCoordChange_dot (i j : atlas H M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (a b : Fin 3 → ℝ) :
    (∑ t : Fin 3, (Q.reduction.rankThreeCoordChange i j x a) t *
      (Q.reduction.rankThreeCoordChange i j x b) t) =
      ∑ t : Fin 3, a t * b t := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let w : E := (‖v‖⁻¹ : ℝ) • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
  let z : E := Q.frames.coordChange i j x w
  have hz : ‖z‖ = 1 := by
    have h := Q.transition_inner i j x hi hj w w
    change inner ℝ z z = inner ℝ w w at h
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hw] at h
    nlinarith [norm_nonneg z]
  calc
    _ = inner ℝ (synth (Q.reduction.Q j)
          (Q.reduction.rankThreeCoordChange i j x a) z)
          (synth (Q.reduction.Q j)
            (Q.reduction.rankThreeCoordChange i j x b) z) := by
        exact (synth_eval_inner _ _ _ z hz).symm
    _ = inner ℝ (Q.frames.coordChange i j x (synth (Q.reduction.Q i) a w))
          (Q.frames.coordChange i j x (synth (Q.reduction.Q i) b w)) := by
        rw [synth_rankThreeCoordChange_eval Q i j x hi hj a w,
          synth_rankThreeCoordChange_eval Q i j x hi hj b w]
    _ = inner ℝ (synth (Q.reduction.Q i) a w)
          (synth (Q.reduction.Q i) b w) :=
        Q.transition_inner i j x hi hj _ _
    _ = _ := synth_eval_inner _ a b w hw

end
end QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
