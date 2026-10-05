import QuaternionicSymmetry.ContinuousWedge
import QuaternionicSymmetry.ContinuousAlternationTransport
import Mathlib.GroupTheory.Perm.Fin

/-! Permutation decomposition by the derivative-slot position. -/

set_option maxHeartbeats 600000

namespace QuaternionicSymmetry.ContinuousWedgeShuffle

open Equiv

noncomputable section

private def cycleInsert {n : ℕ} (i : Fin (n + 1)) (τ : Perm (Fin n)) :
    Perm (Fin (n + 1)) :=
  i.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, τ)

private theorem cycleInsert_zero {n : ℕ} (i : Fin (n + 1)) (τ : Perm (Fin n)) :
    cycleInsert i τ 0 = i := by
  simp [cycleInsert]

private theorem cycleInsert_succ {n : ℕ} (i : Fin (n + 1)) (τ : Perm (Fin n))
    (j : Fin n) : cycleInsert i τ j.succ = i.succAbove (τ j) := by
  simp [cycleInsert]

private theorem decomposeFin_fst {n : ℕ} (σ : Perm (Fin (n + 1))) :
    (Equiv.Perm.decomposeFin σ).1 = σ 0 := by
  simp [Equiv.Perm.decomposeFin]

/-- Decompose a permutation into the image of the first slot and an ordered
permutation of the remaining slots.  The cycle convention makes the sign
`(-1)^i sign(τ)`, exactly the exterior-derivative convention. -/
def cycleDecompose {n : ℕ} : Perm (Fin (n + 1)) ≃
    Fin (n + 1) × Perm (Fin n) where
  toFun σ :=
    let i := σ 0
    (i, (Equiv.Perm.decomposeFin (i.cycleRange * σ)).2)
  invFun x := cycleInsert x.1 x.2
  left_inv σ := by
    change cycleInsert (σ 0) (Equiv.Perm.decomposeFin ((σ 0).cycleRange * σ)).2 = σ
    have hfirst : (Equiv.Perm.decomposeFin ((σ 0).cycleRange * σ)).1 = 0 := by
      rw [decomposeFin_fst]
      simp
    have hpair : Equiv.Perm.decomposeFin ((σ 0).cycleRange * σ) =
        (0, (Equiv.Perm.decomposeFin ((σ 0).cycleRange * σ)).2) := by
      exact Prod.ext hfirst rfl
    have hsymm : Equiv.Perm.decomposeFin.symm
        (0, (Equiv.Perm.decomposeFin ((σ 0).cycleRange * σ)).2) =
        (σ 0).cycleRange * σ := by
      rw [← hpair, Equiv.symm_apply_apply]
    calc
      _ = (σ 0).cycleRange.symm *
          Equiv.Perm.decomposeFin.symm
            (0, (Equiv.Perm.decomposeFin ((σ 0).cycleRange * σ)).2) := rfl
      _ = σ := by
        rw [hsymm]
        change (σ 0).cycleRange⁻¹ * ((σ 0).cycleRange * σ) = σ
        rw [← mul_assoc, inv_mul_cancel, one_mul]
  right_inv x := by
    rcases x with ⟨i, τ⟩
    change (cycleInsert i τ 0,
      (Equiv.Perm.decomposeFin ((cycleInsert i τ 0).cycleRange * cycleInsert i τ)).2) =
        (i, τ)
    simp only [cycleInsert_zero]
    change (i, (Equiv.Perm.decomposeFin
      (i.cycleRange * (i.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, τ)))).2) =
        (i, τ)
    have hc : i.cycleRange *
        (i.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, τ)) =
        Equiv.Perm.decomposeFin.symm (0, τ) := by
      change i.cycleRange *
        (i.cycleRange⁻¹ * Equiv.Perm.decomposeFin.symm (0, τ)) = _
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [hc, Equiv.apply_symm_apply]

theorem cycleDecompose_symm_zero {n : ℕ} (i : Fin (n + 1)) (τ : Perm (Fin n)) :
    cycleDecompose.symm (i, τ) 0 = i := cycleInsert_zero i τ

theorem cycleDecompose_symm_succ {n : ℕ} (i : Fin (n + 1)) (τ : Perm (Fin n))
    (j : Fin n) : cycleDecompose.symm (i, τ) j.succ = i.succAbove (τ j) :=
  cycleInsert_succ i τ j

theorem cycleDecompose_symm_sign {n : ℕ} (i : Fin (n + 1)) (τ : Perm (Fin n)) :
    Equiv.Perm.sign (cycleDecompose.symm (i, τ)) =
      (-1 : ℤ) ^ i.val * Equiv.Perm.sign τ := by
  simp [cycleDecompose, cycleInsert, Equiv.Perm.sign_mul]

/-- Full alternation of a map already alternating in all but its first slot
is `n!` times the insertion alternation.  This is the combinatorial bridge
between the full wedge normalization and `alternatizeUncurryFin`. -/
theorem fullAlternation_eq_factorial_insertion
    {E C : Type*} [AddCommGroup C] {n : ℕ}
    (f : E → (Fin n → E) → C)
    (hf : ∀ (u : E) (w : Fin n → E) (τ : Perm (Fin n)),
      f u (w ∘ τ) = (Equiv.Perm.sign τ : ℤ) • f u w)
    (v : Fin (n + 1) → E) :
    (∑ σ : Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
      f (v (σ 0)) (fun j => v (σ j.succ))) =
      (n.factorial : ℤ) • ∑ i : Fin (n + 1),
        (-1 : ℤ) ^ i.val • f (v i) (i.removeNth v) := by
  have hreindex :
      (∑ σ : Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
        f (v (σ 0)) (fun j => v (σ j.succ))) =
      ∑ x : Fin (n + 1) × Perm (Fin n),
        (Equiv.Perm.sign (cycleDecompose.symm x) : ℤ) •
          f (v (cycleDecompose.symm x 0))
            (fun j => v (cycleDecompose.symm x j.succ)) := by
    exact (Equiv.sum_comp cycleDecompose.symm _).symm
  rw [hreindex]
  simp only [Fintype.sum_prod_type, cycleDecompose_symm_zero,
    cycleDecompose_symm_succ, cycleDecompose_symm_sign]
  have htail (i : Fin (n + 1)) (τ : Perm (Fin n)) :
      f (v i) (fun j => v (i.succAbove (τ j))) =
        (Equiv.Perm.sign τ : ℤ) • f (v i) (i.removeNth v) := by
    simpa only [Fin.removeNth] using hf (v i) (i.removeNth v) τ
  simp_rw [htail]
  simp only [smul_smul]
  have hsign (τ : Perm (Fin n)) :
      (Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign τ : ℤ) = 1 := by
    simpa only [Units.val_mul, Units.val_one] using
      congrArg (fun z : ℤˣ => (z : ℤ)) (Int.units_mul_self (Equiv.Perm.sign τ))
  simp_rw [mul_assoc, hsign, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
  simp only [Nat.cast_smul_eq_nsmul]
  rw [← Finset.smul_sum]
  simp only [Fintype.card_fin]

variable {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup C] [NormedSpace ℝ C] {n : ℕ}

local instance : NormedAddCommGroup (E [⋀^Fin n]→L[ℝ] C) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin n]→L[ℝ] C) := inferInstance

/-- The bounded full alternation of a derivative-slot multilinear map is
`n!` times mathlib's insertion alternation. -/
theorem alternation_uncurryLeft_eq_factorial_insertion
    (D : E →L[ℝ] E [⋀^Fin n]→L[ℝ] C) :
    ContinuousAlternation.alternationCLM
      (((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ) ∘L D).uncurryLeft) =
        (n.factorial : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin D := by
  ext v
  have hf : ∀ (u : E) (w : Fin n → E) (τ : Perm (Fin n)),
      D u (w ∘ τ) = (Equiv.Perm.sign τ : ℤ) • D u w := by
    intro u w τ
    simpa [Function.comp_assoc] using
      (D u).toAlternatingMap.map_congr_perm (w ∘ τ) τ.symm
  have h := fullAlternation_eq_factorial_insertion
    (fun u w => D u w) hf v
  rw [ContinuousAlternation.alternationCLM_apply]
  simp only [ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have h' :
      (∑ σ : Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
        D (v (σ 0)) (fun j => v (σ j.succ))) =
      (n.factorial : ℝ) • ∑ i : Fin (n + 1),
        (-1 : ℤ) ^ i.val • D (v i) (i.removeNth v) := by
    simpa only [Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul] using h
  convert h' using 1

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] {p q : ℕ}

def leftDerivativeRaw (P : A →L[ℝ] B →L[ℝ] C)
    (D : E →L[ℝ] E [⋀^Fin p]→L[ℝ] A)
    (β : E [⋀^Fin q]→L[ℝ] B)
    (v : Fin (p + q + 1) → E) (σ : Perm (Fin (p + q + 1))) : C :=
  P (D (v (σ 0))
      (fun j => v (σ ((finSumFinEquiv (m := p) (n := q) (Sum.inl j)).succ))))
    (β (fun j => v (σ ((finSumFinEquiv (m := p) (n := q) (Sum.inr j)).succ))))

theorem insertion_wedge_left_fullAlt (P : A →L[ℝ] B →L[ℝ] C)
    (D : E →L[ℝ] E [⋀^Fin p]→L[ℝ] A)
    (β : E [⋀^Fin q]→L[ℝ] B) (v : Fin (p + q + 1) → E) :
    (∑ i : Fin (p + q + 1), (-1 : ℤ) ^ i.val •
      ContinuousWedge.wedge P (D (v i)) β (i.removeNth v)) =
      (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) •
        ∑ σ : Perm (Fin (p + q + 1)), Equiv.Perm.sign σ •
          leftDerivativeRaw P D β v σ := by
  rw [← Equiv.sum_comp cycleDecompose.symm]
  simp only [Fintype.sum_prod_type]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousWedge.wedge_apply]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [leftDerivativeRaw, cycleDecompose_symm_zero,
    cycleDecompose_symm_succ, Function.comp_def, Fin.removeNth_apply,
    Units.smul_def, cycleDecompose_symm_sign]
  rw [smul_comm ((-1 : ℤ) ^ i.val)
    (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹)]
  rw [smul_smul]

/-- Reassociating the index set from `(p+1)+q` to `(p+q)+1` preserves
the order derivative, left block, right block. -/
def wedgeLeftIndex (p q : ℕ) : Fin ((p + 1) + q) ≃ Fin (p + q + 1) :=
  finCongr (by omega)

theorem wedgeLeftIndex_zero (p q : ℕ) :
    wedgeLeftIndex p q (finSumFinEquiv (m := p + 1) (n := q)
      (Sum.inl (0 : Fin (p + 1)))) = 0 := by
  apply Fin.ext
  simp [wedgeLeftIndex]

theorem wedgeLeftIndex_left (p q : ℕ) (j : Fin p) :
    wedgeLeftIndex p q (finSumFinEquiv (m := p + 1) (n := q)
      (Sum.inl j.succ)) =
        (finSumFinEquiv (m := p) (n := q) (Sum.inl j)).succ := by
  apply Fin.ext
  simp [wedgeLeftIndex]

theorem wedgeLeftIndex_right (p q : ℕ) (j : Fin q) :
    wedgeLeftIndex p q (finSumFinEquiv (m := p + 1) (n := q)
      (Sum.inr j)) =
        (finSumFinEquiv (m := p) (n := q) (Sum.inr j)).succ := by
  apply Fin.ext
  simp [wedgeLeftIndex, Fin.val_natAdd]
  omega

def leftDerivativeUncurry
    (D : E →L[ℝ] E [⋀^Fin p]→L[ℝ] A) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (p + 1) => E) A :=
  (((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ) ∘L D).uncurryLeft)

private theorem leftDerivativeUncurry_apply
    (D : E →L[ℝ] E [⋀^Fin p]→L[ℝ] A)
    (w : Fin (p + 1) → E) :
    leftDerivativeUncurry D w = D (w 0) (Fin.tail w) := rfl

/-- The raw derivative-first full sum is the full alternation of a single
concatenated multilinear map, transported through the canonical index
associator. -/
theorem leftDerivativeRaw_fullAlt (P : A →L[ℝ] B →L[ℝ] C)
    (D : E →L[ℝ] E [⋀^Fin p]→L[ℝ] A)
    (β : E [⋀^Fin q]→L[ℝ] B) (v : Fin (p + q + 1) → E) :
    (∑ σ : Perm (Fin (p + q + 1)), Equiv.Perm.sign σ •
      leftDerivativeRaw P D β v σ) =
    ContinuousAlternation.alternationCLM
      (((ContinuousMultilinearProduct.concatenate P
        (leftDerivativeUncurry D) β.toContinuousMultilinearMap).domDomCongr
          (finSumFinEquiv (m := p + 1) (n := q))).domDomCongr
            (wedgeLeftIndex p q)) v := by
  rw [ContinuousAlternation.alternationCLM_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have h0 : wedgeLeftIndex p q (Fin.castAdd q (0 : Fin (p + 1))) = 0 := by
    simpa only [finSumFinEquiv_apply_left] using wedgeLeftIndex_zero p q
  have hl (j : Fin p) :
      wedgeLeftIndex p q (Fin.castAdd q j.succ) = (Fin.castAdd q j).succ := by
    simpa only [finSumFinEquiv_apply_left] using wedgeLeftIndex_left p q j
  have hr (j : Fin q) :
      wedgeLeftIndex p q (Fin.natAdd (p + 1) j) = (Fin.natAdd p j).succ := by
    simpa only [finSumFinEquiv_apply_right] using wedgeLeftIndex_right p q j
  simp only [leftDerivativeRaw, leftDerivativeUncurry_apply,
    ContinuousMultilinearProduct.concatenate_apply,
    ContinuousMultilinearMap.domDomCongr_apply,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    Function.comp_apply, h0]
  change _ = P ((D (v (σ 0)))
      (fun j : Fin p => v (σ (wedgeLeftIndex p q (Fin.castAdd q j.succ)))))
    (β (fun j : Fin q => v (σ (wedgeLeftIndex p q (Fin.natAdd (p + 1) j)))))
  simp only [hl, hr]

end
end QuaternionicSymmetry.ContinuousWedgeShuffle
