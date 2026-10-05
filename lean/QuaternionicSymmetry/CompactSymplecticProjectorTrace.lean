import QuaternionicSymmetry.CompactSymplecticProjectorOrbitQuotient
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Concrete spectral invariants of the paired-coordinate projector orbit. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTrace

open Matrix CompactSymplecticProjectiveQuotient CompactSymplecticProjectorOrbit
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- The original paired-coordinate projector has complex trace two. -/
theorem firstPairProjector_trace (n : ℕ) :
    Matrix.trace (firstPairProjector n) = (2 : ℂ) := by
  classical
  simp only [firstPairProjector, Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp
  norm_num

/-- Every actual compact-symplectic conjugate has the same trace. -/
theorem orbitProjector_trace (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    Matrix.trace (orbitProjector n u) = (2 : ℂ) := by
  have hU : (u.1.1 : Matrix _ _ ℂ)ᴴ * (u.1.1 : Matrix _ _ ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self u.1
  calc
    Matrix.trace (orbitProjector n u) =
        Matrix.trace (((u.1 : Matrix _ _ ℂ) * firstPairProjector n) *
          (u.1 : Matrix _ _ ℂ)ᴴ) := rfl
    _ = Matrix.trace ((u.1 : Matrix _ _ ℂ)ᴴ *
          ((u.1 : Matrix _ _ ℂ) * firstPairProjector n)) :=
            Matrix.trace_mul_comm _ _
    _ = Matrix.trace (firstPairProjector n) := by
      rw [← mul_assoc, hU, one_mul]
    _ = 2 := firstPairProjector_trace n

/-- The coordinate projector has complex-linear rank two. -/
theorem firstPairProjector_rank (n : ℕ) :
    (firstPairProjector n).rank = 2 := by
  classical
  rw [firstPairProjector, Matrix.rank_diagonal]
  have hp (i : Fin (n + 1) ⊕ Fin (n + 1)) :
      (if i = Sum.inl (0 : Fin (n + 1)) ∨
          i = Sum.inr (0 : Fin (n + 1)) then (1 : ℂ) else 0) ≠ 0 ↔
        i = Sum.inl (0 : Fin (n + 1)) ∨
          i = Sum.inr (0 : Fin (n + 1)) := by
    by_cases h : i = Sum.inl (0 : Fin (n + 1)) ∨
        i = Sum.inr (0 : Fin (n + 1)) <;> simp [h]
  exact (Fintype.card_congr (Equiv.subtypeEquivRight hp)).trans
    (Fintype.card_subtype_eq_or_eq_of_ne
      (a := Sum.inl (0 : Fin (n + 1)))
      (b := Sum.inr (0 : Fin (n + 1))) (by simp))

/-- Every actual symplectic conjugate is a rank-two Hermitian projector. -/
theorem orbitProjector_rank (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    (orbitProjector n u).rank = 2 := by
  have hu : IsUnit ((u.1.1 : Matrix _ _ ℂ).det) :=
    Matrix.UnitaryGroup.det_isUnit u.1
  have hui : IsUnit (((u⁻¹).1.1 : Matrix _ _ ℂ).det) :=
    Matrix.UnitaryGroup.det_isUnit (u⁻¹).1
  rw [orbitProjector_eq_mul_inverse]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hui]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]
  exact firstPairProjector_rank n

end
end QuaternionicSymmetry.CompactSymplecticProjectorTrace
