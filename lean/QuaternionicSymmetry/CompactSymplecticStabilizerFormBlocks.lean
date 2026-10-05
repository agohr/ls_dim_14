import QuaternionicSymmetry.CompactSymplecticStabilizerUnitaryBlocks

/-! The symplectic form itself splits along the quaternionic first pair.
This supplies the missing bilinear-form input for a genuine block-product
description of the stabilizer. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerFormBlocks

open Matrix CompactSymplecticHaar CompactSymplecticStabilizerIndex
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev J (n : ℕ) := Fin n ⊕ Fin n

private theorem fin_cases_one {α : Type*} (a b : α) :
    Fin.cases a (fun _ : Fin 1 => b) (1 : Fin 2) = b := by
  change Fin.cases a (fun _ : Fin 1 => b) ((0 : Fin 1).succ) = b
  rfl

/-- The standard alternating form, in first-pair/complement coordinates. -/
def blockStandardJ (n : ℕ) : Matrix (Fin 2 ⊕ J n) (Fin 2 ⊕ J n) ℂ :=
  (standardJ (n + 1) : Matrix (I n) (I n) ℂ).reindex
    (blockIndexEquiv n) (blockIndexEquiv n)

private theorem symm_first_one (n : ℕ) :
    (blockIndexEquiv n).symm (Sum.inl (1 : Fin 2)) =
      Sum.inr (0 : Fin (n + 1)) := by
  change Fin.cases (Sum.inl (0 : Fin (n + 1)))
    (fun _ => Sum.inr (0 : Fin (n + 1))) ((0 : Fin 1).succ) = Sum.inr 0
  rfl

theorem blockStandardJ_lower (n : ℕ) :
    (blockStandardJ n).toBlocks₂₂ = standardJ n := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockStandardJ, blockIndexEquiv, standardJ, Matrix.toBlocks₂₂,
      Matrix.fromBlocks, Matrix.reindex_apply, Matrix.one_apply, Fin.succ_inj]

/-- The two-dimensional alternating form is independent of the number of
remaining quaternionic coordinates. -/
def firstBlockJ : Matrix (Fin 2) (Fin 2) ℂ :=
  (blockStandardJ 0).toBlocks₁₁

theorem blockStandardJ_upper (n : ℕ) :
    (blockStandardJ n).toBlocks₁₁ = firstBlockJ := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstBlockJ, blockStandardJ, blockIndexEquiv, standardJ,
      Matrix.toBlocks₁₁, Matrix.fromBlocks, Matrix.reindex_apply,
      Fin.ext_iff, fin_cases_one]

theorem blockStandardJ_upper_right (n : ℕ) :
    (blockStandardJ n).toBlocks₁₂ = 0 := by
  classical
  ext i j
  fin_cases i <;> rcases j with j | j <;>
    (simp only [blockStandardJ, Matrix.toBlocks₁₂, Matrix.reindex_apply,
      symm_first_one]
     simp [blockIndexEquiv, standardJ, Matrix.fromBlocks, Fin.ext_iff,
       fin_cases_one])

theorem blockStandardJ_lower_left (n : ℕ) :
    (blockStandardJ n).toBlocks₂₁ = 0 := by
  classical
  ext i j
  rcases i with i | i <;> fin_cases j <;>
    (simp only [blockStandardJ, Matrix.toBlocks₂₁, Matrix.reindex_apply,
      symm_first_one]
     simp [blockIndexEquiv, standardJ, Matrix.fromBlocks, Fin.ext_iff,
       fin_cases_one])

theorem blockStandardJ_eq_fromBlocks (n : ℕ) :
    blockStandardJ n = Matrix.fromBlocks firstBlockJ 0 0
      (standardJ n) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (blockStandardJ n)]
  rw [blockStandardJ_upper, blockStandardJ_upper_right,
    blockStandardJ_lower_left, blockStandardJ_lower]

end
end QuaternionicSymmetry.CompactSymplecticStabilizerFormBlocks
