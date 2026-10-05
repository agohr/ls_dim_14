import QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric
import QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicRow

/-! The Frobenius norm of an off-diagonal Hermitian block is twice
the entrywise squared norm of its upper block. This is the first
normalization step for the actual projector-base tangent metric. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBlockFrobenius

open Matrix
open scoped Matrix.Norms.Operator
noncomputable section

theorem sum_normSq_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (X : Matrix ι ι ℂ) :
    (∑ i : κ, ∑ j : κ, Complex.normSq ((X.reindex e e) i j)) =
      ∑ i : ι, ∑ j : ι, Complex.normSq (X i j) := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hinner (i : κ) :
      (∑ j : κ, Complex.normSq (X (e.symm i) (e.symm j))) =
        ∑ j : ι, Complex.normSq (X (e.symm i) j) :=
    e.symm.sum_comp (fun j : ι => Complex.normSq (X (e.symm i) j))
  simp_rw [hinner]
  exact e.symm.sum_comp (fun i : ι => ∑ j : ι, Complex.normSq (X i j))

variable {α β : Type*} [Fintype α] [Fintype β]

def offDiagonal (B : Matrix α β ℂ) : Matrix (α ⊕ β) (α ⊕ β) ℂ :=
  Matrix.fromBlocks 0 B Bᴴ 0

theorem offDiagonal_sum_normSq (B : Matrix α β ℂ) :
    (∑ i : α ⊕ β, ∑ j : α ⊕ β,
      Complex.normSq (offDiagonal B i j)) =
      2 * ∑ i : α, ∑ j : β, Complex.normSq (B i j) := by
  classical
  simp only [Fintype.sum_sum_type]
  simp [offDiagonal, Matrix.fromBlocks, Matrix.conjTranspose_apply,
    Complex.normSq_conj]
  rw [show (∑ j : β, ∑ i : α, Complex.normSq (B i j)) =
    (∑ i : α, ∑ j : β, Complex.normSq (B i j)) from Finset.sum_comm]
  ring

theorem offDiagonal_trace_self (B : Matrix α β ℂ) :
    (Matrix.trace ((offDiagonal B)ᴴ * offDiagonal B)).re =
      2 * ∑ i : α, ∑ j : β, Complex.normSq (B i j) := by
  classical
  have hsum : (Matrix.trace ((offDiagonal B)ᴴ * offDiagonal B)).re =
      ∑ i : α ⊕ β, ∑ j : α ⊕ β,
        Complex.normSq (offDiagonal B i j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    simp_rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.re_sum, Complex.ofReal_re]
    exact Finset.sum_comm
  exact hsum.trans (offDiagonal_sum_normSq B)

end

open CompactSymplecticProjectorQuaternionicRow

/-- The second constrained quaternionic row has exactly the same squared
entry norm as the free first row. -/
theorem quaternionicUpper_sum_normSq (n : ℕ)
    (b : (Fin n ⊕ Fin n) → ℂ) :
    (∑ r : Fin 2, ∑ c : Fin n ⊕ Fin n,
      Complex.normSq (upperBlockFromRow n b r c)) =
      2 * ∑ c : Fin n ⊕ Fin n, Complex.normSq (b c) := by
  classical
  simp only [Fin.sum_univ_two, Fintype.sum_sum_type,
    upperBlockFromRow_zero, upperBlockFromRow_one_inl,
    upperBlockFromRow_one_inr, Complex.normSq_neg]
  simp only [Complex.star_def, Complex.normSq_conj]
  ring

/-- The full Hermitian projector tangent matrix has Frobenius square four
times the standard real square of its unrestricted first complex row. -/
theorem quaternionicOffDiagonal_trace_self (n : ℕ)
    (b : (Fin n ⊕ Fin n) → ℂ) :
    (Matrix.trace ((offDiagonal (upperBlockFromRow n b))ᴴ *
      offDiagonal (upperBlockFromRow n b))).re =
      4 * ∑ c : Fin n ⊕ Fin n, Complex.normSq (b c) := by
  rw [offDiagonal_trace_self, quaternionicUpper_sum_normSq]
  ring

theorem quaternionicUpper_trace_self (n : ℕ)
    (B : Matrix (Fin 2) (Fin n ⊕ Fin n) ℂ)
    (hB : B * CompactSymplecticHaar.standardJ n =
      CompactSymplecticStabilizerFormBlocks.firstBlockJ * B.map star) :
    (Matrix.trace ((offDiagonal B)ᴴ * offDiagonal B)).re =
      4 * ∑ c : Fin n ⊕ Fin n, Complex.normSq (B 0 c) := by
  have hrow : upperBlockFromRow n (B 0) = B := by
    have h := (upperBlockRowEquiv n).left_inv
      (⟨B, hB⟩ : QuaternionicUpper n)
    exact congrArg Subtype.val h
  rw [← hrow]
  exact quaternionicOffDiagonal_trace_self n (B 0)

theorem quaternionicUpper_full_sum_normSq (n : ℕ)
    (B : Matrix (Fin 2) (Fin n ⊕ Fin n) ℂ)
    (hB : B * CompactSymplecticHaar.standardJ n =
      CompactSymplecticStabilizerFormBlocks.firstBlockJ * B.map star) :
    (∑ i : Fin 2 ⊕ (Fin n ⊕ Fin n),
      ∑ j : Fin 2 ⊕ (Fin n ⊕ Fin n),
        Complex.normSq (offDiagonal B i j)) =
      4 * ∑ c : Fin n ⊕ Fin n, Complex.normSq (B 0 c) := by
  have hrow : upperBlockFromRow n (B 0) = B := by
    exact congrArg Subtype.val
      ((upperBlockRowEquiv n).left_inv (⟨B, hB⟩ : QuaternionicUpper n))
  rw [← hrow, offDiagonal_sum_normSq, quaternionicUpper_sum_normSq]
  simp only [upperBlockFromRow_zero]
  ring

end QuaternionicSymmetry.CompactSymplecticProjectorBlockFrobenius
