import QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicBlock

/-! Row coordinates for the first-pair quaternionic mixed block. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicRow

open Matrix
open CompactSymplecticStabilizerFormBlocks
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev BMat (n : ℕ) := Matrix (Fin 2) (J n) ℂ

private theorem fin_cases_one {α : Type*} (a b : α) :
    Fin.cases a (fun _ : Fin 1 => b) (1 : Fin 2) = b := by
  change Fin.cases a (fun _ : Fin 1 => b) ((0 : Fin 1).succ) = b
  rfl

/-- The first quaternionic-line alternating form has the literal
two-by-two standard entries. -/
theorem firstBlockJ_zero_zero : firstBlockJ 0 0 = 0 := by
  simp [firstBlockJ, blockStandardJ, CompactSymplecticHaar.standardJ,
    CompactSymplecticStabilizerIndex.blockIndexEquiv,
    Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.fromBlocks]

theorem firstBlockJ_zero_one : firstBlockJ 0 1 = 1 := by
  simp [firstBlockJ, blockStandardJ, CompactSymplecticHaar.standardJ,
    CompactSymplecticStabilizerIndex.blockIndexEquiv,
    Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.fromBlocks,
    fin_cases_one]

theorem firstBlockJ_one_zero : firstBlockJ 1 0 = -1 := by
  simp [firstBlockJ, blockStandardJ, CompactSymplecticHaar.standardJ,
    CompactSymplecticStabilizerIndex.blockIndexEquiv,
    Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.fromBlocks,
    fin_cases_one]

theorem firstBlockJ_one_one : firstBlockJ 1 1 = 0 := by
  simp [firstBlockJ, blockStandardJ, CompactSymplecticHaar.standardJ,
    CompactSymplecticStabilizerIndex.blockIndexEquiv,
    Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.fromBlocks,
    fin_cases_one]

theorem mul_standardJ_inl (n : ℕ) (B : BMat n)
    (r : Fin 2) (j : Fin n) :
    (B * CompactSymplecticHaar.standardJ n) r (Sum.inl j) =
      -B r (Sum.inr j) := by
  classical
  simp [CompactSymplecticHaar.standardJ, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem mul_standardJ_inr (n : ℕ) (B : BMat n)
    (r : Fin 2) (j : Fin n) :
    (B * CompactSymplecticHaar.standardJ n) r (Sum.inr j) =
      B r (Sum.inl j) := by
  classical
  simp [CompactSymplecticHaar.standardJ, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem firstBlockJ_mul_zero (n : ℕ) (B : BMat n) (c : J n) :
    (firstBlockJ * B.map star) 0 c = star (B 1 c) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, firstBlockJ_zero_zero,
    firstBlockJ_zero_one]

theorem firstBlockJ_mul_one (n : ℕ) (B : BMat n) (c : J n) :
    (firstBlockJ * B.map star) 1 c = -star (B 0 c) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, firstBlockJ_one_zero,
    firstBlockJ_one_one]

theorem quaternionic_row_one_inl (n : ℕ) (B : BMat n)
    (hB : B * CompactSymplecticHaar.standardJ n = firstBlockJ * B.map star)
    (j : Fin n) :
    B 1 (Sum.inl j) = -star (B 0 (Sum.inr j)) := by
  have h := congrArg (fun C : BMat n => C 1 (Sum.inr j)) hB
  simpa only [mul_standardJ_inr, firstBlockJ_mul_one] using h

theorem quaternionic_row_one_inr (n : ℕ) (B : BMat n)
    (hB : B * CompactSymplecticHaar.standardJ n = firstBlockJ * B.map star)
    (j : Fin n) :
    B 1 (Sum.inr j) = star (B 0 (Sum.inl j)) := by
  have h := congrArg (fun C : BMat n => C 1 (Sum.inl j)) hB
  simp only [mul_standardJ_inl, firstBlockJ_mul_one] at h
  exact neg_inj.mp h

/-- Construct the full quaternionic mixed block from its unrestricted
first complex row. -/
def upperBlockFromRow (n : ℕ) (b : J n → ℂ) : BMat n :=
  fun r c => Fin.cases (b c)
    (fun _ => match c with
      | Sum.inl j => -star (b (Sum.inr j))
      | Sum.inr j => star (b (Sum.inl j))) r

@[simp] theorem upperBlockFromRow_zero (n : ℕ) (b : J n → ℂ) (c : J n) :
    upperBlockFromRow n b 0 c = b c := rfl

@[simp] theorem upperBlockFromRow_one_inl (n : ℕ) (b : J n → ℂ) (j : Fin n) :
    upperBlockFromRow n b 1 (Sum.inl j) = -star (b (Sum.inr j)) := by
  simp [upperBlockFromRow, fin_cases_one]

@[simp] theorem upperBlockFromRow_one_inr (n : ℕ) (b : J n → ℂ) (j : Fin n) :
    upperBlockFromRow n b 1 (Sum.inr j) = star (b (Sum.inl j)) := by
  simp [upperBlockFromRow, fin_cases_one]

theorem upperBlockFromRow_quaternionic (n : ℕ) (b : J n → ℂ) :
    upperBlockFromRow n b * CompactSymplecticHaar.standardJ n =
      firstBlockJ * (upperBlockFromRow n b).map star := by
  ext r c
  have hr : r = 0 ∨ r = 1 := by fin_cases r <;> simp
  rcases hr with rfl | rfl <;> rcases c with j | j
  · rw [mul_standardJ_inl, firstBlockJ_mul_zero]
    simp
  · rw [mul_standardJ_inr, firstBlockJ_mul_zero]
    simp
  · rw [mul_standardJ_inl, firstBlockJ_mul_one]
    simp
  · rw [mul_standardJ_inr, firstBlockJ_mul_one]
    simp

/-- The actual quaternionic mixed-block equation as a concrete subtype. -/
def QuaternionicUpper (n : ℕ) :=
  {B : BMat n // B * CompactSymplecticHaar.standardJ n =
    firstBlockJ * B.map star}

/-- The first row is a complete and unrestricted coordinate for every
quaternionic upper mixed block. -/
def upperBlockRowEquiv (n : ℕ) : QuaternionicUpper n ≃ (J n → ℂ) where
  toFun B := B.1 0
  invFun b := ⟨upperBlockFromRow n b, upperBlockFromRow_quaternionic n b⟩
  left_inv := by
    intro ⟨B, hB⟩
    apply Subtype.ext
    ext r c
    have hr : r = 0 ∨ r = 1 := by fin_cases r <;> simp
    rcases hr with rfl | rfl
    · simp
    · rcases c with j | j
      · simpa using (quaternionic_row_one_inl n B hB j).symm
      · simpa using (quaternionic_row_one_inr n B hB j).symm
  right_inv := by
    intro b
    rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicRow
