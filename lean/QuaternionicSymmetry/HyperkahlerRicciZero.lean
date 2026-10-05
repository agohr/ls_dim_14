import QuaternionicSymmetry.QuaternionicEigenbasisFinite
import Mathlib.Analysis.InnerProductSpace.Trace

/-! A quaternionic-linear algebraic curvature tensor has zero Ricci trace.
The cancellation already holds on each quaternionic basis line. -/
namespace QuaternionicSymmetry.HyperkahlerRicciZero
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (S : QuaternionicStructure E)
  (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)

def tensor (u v w z : E) : ℝ := inner ℝ (R u v w) z

set_option maxHeartbeats 800000 in
theorem quartet_zero
    (hf : ∀ u v w z, tensor R u v w z = -tensor R v u w z)
    (hl : ∀ u v w z, tensor R u v w z = -tensor R u v z w)
    (hp : ∀ u v w z, tensor R u v w z = tensor R w z u v)
    (hB : ∀ u v w z, tensor R u v w z + tensor R v w u z +
      tensor R w u v z = 0)
    (hI : ∀ u v w, R u v (S.I w) = S.I (R u v w))
    (hJ : ∀ u v w, R u v (S.J w) = S.J (R u v w))
    (e v w : E) :
    tensor R e v w e + tensor R (S.I e) v w (S.I e) +
      tensor R (S.J e) v w (S.J e) + tensor R (S.K e) v w (S.K e) = 0 := by
  have hIl (u v w z : E) : tensor R u v (S.I w) (S.I z) = tensor R u v w z := by
    dsimp only [tensor]
    rw [hI, S.I.inner_map_map]
  have hJl (u v w z : E) : tensor R u v (S.J w) (S.J z) = tensor R u v w z := by
    dsimp only [tensor]
    rw [hJ, S.J.inner_map_map]
  have hKl (u v w z : E) : tensor R u v (S.K w) (S.K z) = tensor R u v w z := by
    change tensor R u v (S.I (S.J w)) (S.I (S.J z)) = _
    rw [hIl, hJl]
  have hJf (u v w z : E) : tensor R (S.J u) (S.J v) w z = tensor R u v w z := by
    rw [hp, hJl, ← hp]
  have h₁ : tensor R (S.I e) v e (S.I w) =
      tensor R (S.I e) v w (S.I e) := by
    rw [← hIl (S.I e) v e (S.I w), S.I_sq]
    simp only [tensor, inner_neg_right]
    exact hl (S.I e) v w (S.I e) |>.symm
  have h₂ : tensor R v e (S.I e) (S.I w) = tensor R e v w e := by
    rw [hIl, hf v e, hl e v e w]
    ring
  have hb₁ := hB e (S.I e) v (S.I w)
  rw [h₁, h₂] at hb₁
  have h₃ : tensor R e (S.I e) (S.J v) (S.K w) =
      -tensor R e (S.I e) v (S.I w) := by
    rw [← hJl e (S.I e) (S.J v) (S.K w)]
    simp only [S.J_sq, S.K_apply, S.J_I_anti, map_neg]
    simp only [S.J_sq, map_neg, ContinuousLinearMap.neg_apply, neg_neg, tensor, inner_neg_left]
  have h₄ : tensor R (S.I e) (S.J v) e (S.K w) =
      tensor R (S.K e) v w (S.K e) := by
    rw [← hJf (S.I e) (S.J v) e (S.K w)]
    simp only [S.J_I_anti, S.J_sq, ← S.K_apply, tensor, map_neg, ContinuousLinearMap.neg_apply, neg_neg]
    change tensor R (S.K e) v e (S.K w) = _
    rw [← hKl (S.K e) v e (S.K w), S.K_sq]
    simp only [tensor, inner_neg_right]
    exact hl (S.K e) v w (S.K e) |>.symm
  have h₅ : tensor R (S.J v) e (S.I e) (S.K w) =
      tensor R (S.J e) v w (S.J e) := by
    rw [← hJf (S.J v) e (S.I e) (S.K w), S.J_sq]
    simp only [tensor, map_neg, ContinuousLinearMap.neg_apply, inner_neg_left]
    change -tensor R v (S.J e) (S.I e) (S.K w) = _
    rw [hf v (S.J e), neg_neg]
    rw [← hIl (S.J e) v (S.I e) (S.K w)]
    simp only [S.I_sq, S.K_apply, tensor, map_neg, ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right, neg_neg]
    change tensor R (S.J e) v e (S.J w) = _
    rw [← hJl (S.J e) v e (S.J w), S.J_sq]
    simp only [tensor, inner_neg_right]
    exact hl (S.J e) v w (S.J e) |>.symm
  have hb₂ := hB e (S.I e) (S.J v) (S.K w)
  rw [h₃, h₄, h₅] at hb₂
  linarith

theorem ricci_zero
    (hf : ∀ u v w z, tensor R u v w z = -tensor R v u w z)
    (hl : ∀ u v w z, tensor R u v w z = -tensor R u v z w)
    (hp : ∀ u v w z, tensor R u v w z = tensor R w z u v)
    (hB : ∀ u v w z, tensor R u v w z + tensor R v w u z +
      tensor R w u v z = 0)
    (hI : ∀ u v w, R u v (S.I w) = S.I (R u v w))
    (hJ : ∀ u v w, R u v (S.J w) = S.J (R u v w))
    (v w : E) :
    (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (R (stdOrthonormalBasis ℝ E a) v w)
        (stdOrthonormalBasis ℝ E a)) = 0 := by
  classical
  obtain ⟨vals, e, b, hb, _⟩ :=
    S.exists_eigenOrthonormalBasis_fin 0 S.skewCentralizer.zero_mem
  let T : E →L[ℝ] E := (ContinuousLinearMap.apply ℝ E w).comp (R.flip v)
  have hbtrace : LinearMap.trace ℝ E T.toLinearMap = 0 := by
    rw [LinearMap.trace_eq_sum_inner _ b, Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro j _
    simp only [Fin.sum_univ_four]
    simp only [T, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.flip_apply]
    simpa [hb, QuaternionicStructure.frame, tensor, real_inner_comm,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] using
      quartet_zero S R hf hl hp hB hI hJ (e j) v w
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)] at hbtrace
  simpa only [T, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.flip_apply, real_inner_comm]
    using hbtrace

end
end QuaternionicSymmetry.HyperkahlerRicciZero
