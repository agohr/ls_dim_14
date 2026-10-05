import QuaternionicSymmetry.ContinuousWedgeShuffle
import QuaternionicSymmetry.ContinuousWedgeBlockAlternation

/-! The insertion sum for differentiating the right factor of a normalized
continuous wedge, rewritten as a single full alternation. -/

namespace QuaternionicSymmetry.ContinuousWedgeRightInsertion

open Equiv
open QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeShuffle
  QuaternionicSymmetry.ContinuousWedgeBlockAlternation
  QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousMultilinearProduct

noncomputable section

variable {E A B C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  {p q : ℕ}

private def rawRight (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (D : E → E [⋀^Fin q]→L[ℝ] B)
    (v : Fin (p + q + 1) → E) (σ : Perm (Fin (p + q + 1))) : C :=
  P (α (fun j => v (σ ((finSumFinEquiv (m := p) (n := q) (Sum.inl j)).succ))))
    (D (v (σ 0))
      (fun j => v (σ ((finSumFinEquiv (m := p) (n := q) (Sum.inr j)).succ))))

theorem fullAlt_rawRight_eq_insertion (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (D : E → E [⋀^Fin q]→L[ℝ] B)
    (v : Fin (p + q + 1) → E) :
    (∑ σ : Perm (Fin (p + q + 1)), (Equiv.Perm.sign σ : ℤ) •
      rawRight P α D v σ) =
    ∑ i : Fin (p + q + 1), (-1 : ℤ) ^ i.val •
      ∑ τ : Perm (Fin (p + q)), (Equiv.Perm.sign τ : ℤ) •
        P (α (fun j => (i.removeNth v)
            (τ (finSumFinEquiv (m := p) (n := q) (Sum.inl j)))))
          (D (v i) (fun j => (i.removeNth v)
            (τ (finSumFinEquiv (m := p) (n := q) (Sum.inr j))))) := by
  have hreindex :
      (∑ σ : Perm (Fin (p + q + 1)), (Equiv.Perm.sign σ : ℤ) •
        rawRight P α D v σ) =
      ∑ z : Fin (p + q + 1) × Perm (Fin (p + q)),
        (Equiv.Perm.sign (cycleDecompose.symm z) : ℤ) •
          rawRight P α D v (cycleDecompose.symm z) := by
    exact (Equiv.sum_comp cycleDecompose.symm _).symm
  rw [hreindex]
  simp only [Fintype.sum_prod_type, cycleDecompose_symm_sign, mul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro τ hτ
  congr 1
  simp only [rawRight, cycleDecompose_symm_zero,
    cycleDecompose_symm_succ, Fin.removeNth]

/-- Right-slot exterior differentiation is the full alternation of its raw
coefficient derivative, with exactly the `1/(p!q!)` wedge normalization. -/
theorem insertion_wedge_right_fullAlt (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (D : E → E [⋀^Fin q]→L[ℝ] B)
    (v : Fin (p + q + 1) → E) :
    (∑ i : Fin (p + q + 1), (-1 : ℤ) ^ i.val •
      wedge P α (D (v i)) (i.removeNth v)) =
    (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) •
      ∑ σ : Perm (Fin (p + q + 1)), (Equiv.Perm.sign σ : ℤ) •
        rawRight P α D v σ := by
  rw [fullAlt_rawRight_eq_insertion]
  simp_rw [wedge_apply]
  simp only [Finset.smul_sum, smul_smul, Function.comp_def]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro τ hτ
  let a : C := P (α (fun j => i.removeNth v
    (τ (finSumFinEquiv (m := p) (n := q) (Sum.inl j)))))
      (D (v i) (fun j => i.removeNth v
        (τ (finSumFinEquiv (m := p) (n := q) (Sum.inr j)))))
  change (-1 : ℤ) ^ i.val •
      (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) •
        (Equiv.Perm.sign τ : ℤ) • a =
    (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) •
      ((-1 : ℤ) ^ i.val * (Equiv.Perm.sign τ : ℤ)) • a
  rw [smul_comm ((-1 : ℤ) ^ i.val)
    (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹)
    ((Equiv.Perm.sign τ : ℤ) • a), mul_smul]

/-- Move the derivative slot from the front of a full alternation across
the left `p`-block. -/
def blockCross : Perm (Fin (p + q + 1)) :=
  (⟨p, by omega⟩ : Fin (p + q + 1)).cycleRange.symm

theorem blockCross_sign :
    Equiv.Perm.sign (blockCross (p := p) (q := q)) = (-1) ^ p := by
  simp [blockCross]

theorem blockCross_zero :
    blockCross (p := p) (q := q) 0 = (⟨p, by omega⟩ : Fin (p + q + 1)) := by
  simp [blockCross]

theorem blockCross_left (j : Fin p) :
    blockCross (p := p) (q := q)
      ((finSumFinEquiv (m := p) (n := q) (Sum.inl j)).succ) =
        (Fin.castAdd q j).castSucc := by
  have hlt : (Fin.castAdd q j).castSucc <
      (⟨p, by omega⟩ : Fin (p + q + 1)) := by
    apply Fin.lt_def.mpr
    simp only [Fin.val_castSucc, Fin.val_castAdd]
    exact j.isLt
  simp only [blockCross, finSumFinEquiv_apply_left,
    Fin.cycleRange_symm_succ]
  exact Fin.succAbove_of_castSucc_lt _ _ hlt

theorem blockCross_right (j : Fin q) :
    blockCross (p := p) (q := q)
      ((finSumFinEquiv (m := p) (n := q) (Sum.inr j)).succ) =
        (Fin.natAdd p j).succ := by
  have hle : (⟨p, by omega⟩ : Fin (p + q + 1)) ≤
      (Fin.natAdd p j).castSucc := by
    apply Fin.le_def.mpr
    simp only [Fin.val_castSucc, Fin.val_natAdd]
    omega
  simp only [blockCross, finSumFinEquiv_apply_right,
    Fin.cycleRange_symm_succ]
  exact Fin.succAbove_of_le_castSucc _ _ hle

private def rawShifted (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (D : E → E [⋀^Fin q]→L[ℝ] B)
    (v : Fin (p + q + 1) → E) (σ : Perm (Fin (p + q + 1))) : C :=
  P (α (fun j => v (σ (Fin.castSucc (Fin.castAdd q j)))))
    (D (v (σ (⟨p, by omega⟩ : Fin (p + q + 1))))
      (fun j => v (σ (Fin.natAdd p j).succ)))

private theorem rawRight_blockCross (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (D : E → E [⋀^Fin q]→L[ℝ] B)
    (v : Fin (p + q + 1) → E) (σ : Perm (Fin (p + q + 1))) :
    rawRight P α D v (σ * blockCross (p := p) (q := q)) =
      rawShifted P α D v σ := by
  simp only [rawRight, rawShifted, Equiv.Perm.mul_apply,
    blockCross_zero, blockCross_left, blockCross_right]

/-- Crossing the derivative slot over the `p` left inputs contributes the
Koszul sign `(-1)^p` to the complete signed alternation. -/
theorem fullAlt_rawShifted_eq_sign_rawRight
    (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (D : E → E [⋀^Fin q]→L[ℝ] B)
    (v : Fin (p + q + 1) → E) :
    (∑ σ : Perm (Fin (p + q + 1)), (Equiv.Perm.sign σ : ℤ) •
      rawShifted P α D v σ) =
    (-1 : ℤ) ^ p •
      ∑ σ : Perm (Fin (p + q + 1)), (Equiv.Perm.sign σ : ℤ) •
        rawRight P α D v σ := by
  let ρ := blockCross (p := p) (q := q)
  have hshift : ∀ σ : Perm (Fin (p + q + 1)),
      rawShifted P α D v σ = rawRight P α D v (σ * ρ) := by
    intro σ
    exact (rawRight_blockCross P α D v σ).symm
  simp_rw [hshift]
  have hreindex :
      (∑ σ : Perm (Fin (p + q + 1)), (Equiv.Perm.sign σ : ℤ) •
        rawRight P α D v (σ * ρ)) =
      ∑ τ : Perm (Fin (p + q + 1)),
        (Equiv.Perm.sign (τ * ρ⁻¹) : ℤ) • rawRight P α D v τ := by
    simpa using (Equiv.sum_comp (Equiv.mulRight ρ)
      (fun τ : Perm (Fin (p + q + 1)) =>
        (Equiv.Perm.sign (τ * ρ⁻¹) : ℤ) • rawRight P α D v τ))
  rw [hreindex]
  have hsign (τ : Perm (Fin (p + q + 1))) :
      (Equiv.Perm.sign (τ * ρ⁻¹) : ℤ) =
        (-1 : ℤ) ^ p * (Equiv.Perm.sign τ : ℤ) := by
    simp [Equiv.Perm.sign_mul, ρ, blockCross_sign, mul_comm]
  simp_rw [hsign, mul_smul]
  rw [Finset.smul_sum]

/-- The normalized wedge with an insertion-alternated right factor is the
full alternation with the derivative slot immediately after the left block. -/
theorem wedge_alternatizeUncurryFin_right_eq_rawShifted
    (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A)
    (D : E →L[ℝ] E [⋀^Fin q]→L[ℝ] B)
    (v : Fin (p + q + 1) → E) :
    wedge P α (ContinuousAlternatingMap.alternatizeUncurryFin D) v =
    (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) •
      ∑ σ : Perm (Fin (p + q + 1)), (Equiv.Perm.sign σ : ℤ) •
        rawShifted P α (fun u => D u) v σ := by
  let U : ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => E) B :=
    (((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ) ∘L D).uncurryLeft)
  let W : E [⋀^Fin (p + q + 1)]→L[ℝ] C :=
    alternationCLM ((concatenate P α.toContinuousMultilinearMap U).domDomCongr
      (finSumFinEquiv (m := p) (n := q + 1)))
  have hD : alternationCLM U =
      (q.factorial : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin D :=
    alternation_uncurryLeft_eq_factorial_insertion D
  have hq : (q.factorial : ℝ) ≠ 0 := by positivity
  have hD' : ContinuousAlternatingMap.alternatizeUncurryFin D =
      (q.factorial : ℝ)⁻¹ • alternationCLM U := by
    rw [hD]
    simp [smul_smul, hq]
  have hfactor := alternation_concatenate_right_fin P
    α.toContinuousMultilinearMap U
  have hscalar :
      (q.factorial : ℝ)⁻¹ *
          (((p.factorial * (q + 1).factorial : ℕ) : ℝ)⁻¹) *
            ((q + 1).factorial : ℝ) =
        (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) := by
    have hp : (p.factorial : ℝ) ≠ 0 := by positivity
    have hqs : ((q + 1).factorial : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_mul]
    field_simp
  have hform :
      wedge P α (ContinuousAlternatingMap.alternatizeUncurryFin D) =
        (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) • W := by
    rw [hD', wedge_smul_right]
    change (q.factorial : ℝ)⁻¹ •
      ((((p.factorial * (q + 1).factorial : ℕ) : ℝ)⁻¹) •
        alternationCLM ((concatenate P α.toContinuousMultilinearMap
          (alternationCLM U).toContinuousMultilinearMap).domDomCongr
            (finSumFinEquiv (m := p) (n := q + 1)))) = _
    rw [hfactor]
    simp only [smul_smul]
    rw [← mul_assoc, hscalar]
    rfl
  rw [hform]
  change (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) • W v = _
  congr 1
  change alternationCLM
      ((concatenate P α.toContinuousMultilinearMap U).domDomCongr
        (finSumFinEquiv (m := p) (n := q + 1))) v = _
  rw [alternationCLM_apply]
  congr 1

/-- The right contribution to the graded exterior Leibniz rule.  The
derivative slot crosses the `p` inputs of the left factor, giving `(-1)^p`.
This theorem is the exact pointwise identity used by `extDeriv_wedge`. -/
theorem insertion_wedge_right_eq_signed_wedge_ext
    (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A)
    (D : E →L[ℝ] E [⋀^Fin q]→L[ℝ] B)
    (v : Fin (p + q + 1) → E) :
    (∑ i : Fin (p + q + 1), (-1 : ℤ) ^ i.val •
      wedge P α (D (v i)) (i.removeNth v)) =
    (-1 : ℤ) ^ p •
      wedge P α (ContinuousAlternatingMap.alternatizeUncurryFin D) v := by
  let r : ℝ := (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹)
  let S : C := ∑ σ : Perm (Fin (p + q + 1)),
    (Equiv.Perm.sign σ : ℤ) • rawRight P α (fun u => D u) v σ
  let S' : C := ∑ σ : Perm (Fin (p + q + 1)),
    (Equiv.Perm.sign σ : ℤ) • rawShifted P α (fun u => D u) v σ
  have h₁ : (∑ i : Fin (p + q + 1), (-1 : ℤ) ^ i.val •
      wedge P α (D (v i)) (i.removeNth v)) = r • S :=
    insertion_wedge_right_fullAlt P α (fun u => D u) v
  have h₂ : wedge P α (ContinuousAlternatingMap.alternatizeUncurryFin D) v =
      r • S' := wedge_alternatizeUncurryFin_right_eq_rawShifted P α D v
  have h₃ : S' = (-1 : ℤ) ^ p • S :=
    fullAlt_rawShifted_eq_sign_rawRight P α (fun u => D u) v
  have hsign : (-1 : ℤ) ^ p * (-1 : ℤ) ^ p = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  symm
  calc
    (-1 : ℤ) ^ p • wedge P α
        (ContinuousAlternatingMap.alternatizeUncurryFin D) v =
      (-1 : ℤ) ^ p • (r • S') := by rw [h₂]
    _ = r • ((-1 : ℤ) ^ p • S') := smul_comm _ _ _
    _ = r • ((-1 : ℤ) ^ p • ((-1 : ℤ) ^ p • S)) := by rw [h₃]
    _ = r • S := by rw [smul_smul, hsign, one_smul]
    _ = _ := h₁.symm

end
end QuaternionicSymmetry.ContinuousWedgeRightInsertion
