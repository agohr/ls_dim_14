import QuaternionicSymmetry.ContinuousWedge

/-! The normalized scalar wedge has the constant zero-form as a unit. -/

namespace QuaternionicSymmetry.ContinuousWedgeUnit

open QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousMultilinearProduct
  QuaternionicSymmetry.ContinuousWedge

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ}

def oneZero : E [⋀^Fin 0]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1

def castAlt {m n : ℕ} (h : m = n)
    (α : E [⋀^Fin m]→L[ℝ] ℝ) : E [⋀^Fin n]→L[ℝ] ℝ := by
  cases h
  exact α

theorem castAlt_apply {m n : ℕ} (h : m = n)
    (α : E [⋀^Fin m]→L[ℝ] ℝ) (v : Fin n → E) :
    castAlt h α v = α (v ∘ finCongr h) := by
  cases h
  rfl

theorem wedge_one_left (α : E [⋀^Fin n]→L[ℝ] ℝ) :
    wedge (ContinuousLinearMap.mul ℝ ℝ) oneZero α =
      castAlt (Nat.zero_add n).symm α := by
  have hraw :
      (concatenate (ContinuousLinearMap.mul ℝ ℝ)
        oneZero.toContinuousMultilinearMap
        α.toContinuousMultilinearMap).domDomCongr
          (finSumFinEquiv (m := 0) (n := n)) =
        (castAlt (Nat.zero_add n).symm α).toContinuousMultilinearMap := by
    ext v
    simp [oneZero, ContinuousMultilinearMap.domDomCongr_apply,
      concatenate_apply, castAlt_apply]
    have hv : (fun i : Fin n => v (finSumFinEquiv (Sum.inr i))) =
        v ∘ finCongr (Nat.zero_add n).symm := by
      funext i
      apply congrArg v
      apply Fin.ext
      simp [finSumFinEquiv_apply_right]
    exact congrArg α hv
  unfold wedge
  rw [hraw, alternation_of_alternating]
  simp only [Nat.factorial_zero, one_mul, Fintype.card_fin]
  have hne : (n.factorial : ℝ) ≠ 0 := by positivity
  ext v
  simp [ContinuousAlternatingMap.smul_apply, nsmul_eq_mul, hne]

theorem wedge_one_right (α : E [⋀^Fin n]→L[ℝ] ℝ) :
    wedge (ContinuousLinearMap.mul ℝ ℝ) α oneZero = α := by
  have hraw :
      (concatenate (ContinuousLinearMap.mul ℝ ℝ)
        α.toContinuousMultilinearMap
        oneZero.toContinuousMultilinearMap).domDomCongr
          (finSumFinEquiv (m := n) (n := 0)) =
        α.toContinuousMultilinearMap := by
    ext v
    simp [oneZero, ContinuousMultilinearMap.domDomCongr_apply,
      concatenate_apply]
    have hv : (fun i : Fin n => v (finSumFinEquiv (Sum.inl i))) = v := by
      funext i
      apply congrArg v
      apply Fin.ext
      change (Fin.castAdd 0 i).val = i.val
      rfl
    exact congrArg α hv
  unfold wedge
  rw [hraw, alternation_of_alternating]
  simp only [Nat.factorial_zero, mul_one, Fintype.card_fin]
  have hne : (n.factorial : ℝ) ≠ 0 := by positivity
  ext v
  simp [ContinuousAlternatingMap.smul_apply, nsmul_eq_mul, hne]

end
end QuaternionicSymmetry.ContinuousWedgeUnit
