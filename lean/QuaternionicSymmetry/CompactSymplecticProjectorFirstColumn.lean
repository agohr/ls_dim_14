import QuaternionicSymmetry.QuaternionicMatrixModel
import QuaternionicSymmetry.CompactSymplecticProjectorOrbit

/-! The two columns of a compact-symplectic matrix over the first quaternionic
coordinate are determined by its first complex column. This is the first
algebraic ingredient of a sphere parametrization of the projector orbit. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFirstColumn

open Matrix CompactSymplecticHaar
open CompactSymplecticProjectiveQuotient CompactSymplecticProjectorOrbit
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

theorem first_pair_column_inl (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) (i : Fin (n + 1)) :
    (u.1.1 : Matrix (I n) (I n) ℂ) (Sum.inl i) (Sum.inr 0) =
      -star ((u.1.1 : Matrix (I n) (I n) ℂ) (Sum.inr i) (Sum.inl 0)) := by
  classical
  have h := congrArg (fun M : Matrix (I n) (I n) ℂ => M (Sum.inl i) (Sum.inl 0))
    ((QuaternionicMatrixModel.unitary_mem_stabilizer_iff_commutes_J (n + 1) u.1).mp u.2)
  simp [CompactSymplecticHaar.standardJ, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply] at h
  simpa only [neg_neg] using congrArg Neg.neg h

theorem first_pair_column_inr (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) (i : Fin (n + 1)) :
    (u.1.1 : Matrix (I n) (I n) ℂ) (Sum.inr i) (Sum.inr 0) =
      star ((u.1.1 : Matrix (I n) (I n) ℂ) (Sum.inl i) (Sum.inl 0)) := by
  classical
  have h := congrArg (fun M : Matrix (I n) (I n) ℂ => M (Sum.inr i) (Sum.inl 0))
    ((QuaternionicMatrixModel.unitary_mem_stabilizer_iff_commutes_J (n + 1) u.1).mp u.2)
  simpa [CompactSymplecticHaar.standardJ, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply] using h

/-- Every orbit projector is the sum of the two outer products of the
quaternionically paired first columns. -/
theorem orbitProjector_two_columns (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) (i j : I n) :
    orbitProjector n u i j =
      (u.1.1 : Matrix (I n) (I n) ℂ) i (Sum.inl 0) *
          star ((u.1.1 : Matrix (I n) (I n) ℂ) j (Sum.inl 0)) +
      (u.1.1 : Matrix (I n) (I n) ℂ) i (Sum.inr 0) *
          star ((u.1.1 : Matrix (I n) (I n) ℂ) j (Sum.inr 0)) := by
  classical
  change ((u.1.1 * firstPairProjector n) * u.1.1ᴴ) i j = _
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  simp [firstPairProjector, Fintype.sum_sum_type]

/-- The first complex column of the symplectic matrix. -/
def firstColumn (n : ℕ) (u : CompactSymplecticHaar.Group (n + 1)) : I n → ℂ :=
  fun i => u.1.1 i (Sum.inl 0)

/-- Its forced quaternionic mate. -/
def pairedColumn (n : ℕ) (v : I n → ℂ) : I n → ℂ
  | Sum.inl i => -star (v (Sum.inr i))
  | Sum.inr i => star (v (Sum.inl i))

theorem secondColumn_eq_pairedColumn (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    (fun i => u.1.1 i (Sum.inr 0)) = pairedColumn n (firstColumn n u) := by
  funext i
  cases i with
  | inl k => exact first_pair_column_inl n u k
  | inr k => exact first_pair_column_inr n u k

/-- Rank-two projector formula depending only on a single complex column. -/
def columnProjector (n : ℕ) (v : I n → ℂ) : Matrix (I n) (I n) ℂ :=
  fun i j => v i * star (v j) + pairedColumn n v i * star (pairedColumn n v j)

theorem orbitProjector_eq_columnProjector (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    orbitProjector n u = columnProjector n (firstColumn n u) := by
  ext i j
  rw [orbitProjector_two_columns]
  change _ = firstColumn n u i * star (firstColumn n u j) +
    pairedColumn n (firstColumn n u) i * star (pairedColumn n (firstColumn n u) j)
  rw [← secondColumn_eq_pairedColumn n u]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorFirstColumn
