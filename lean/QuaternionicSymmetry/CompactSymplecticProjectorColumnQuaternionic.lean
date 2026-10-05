import QuaternionicSymmetry.CompactSymplecticProjectorColumnIdempotent

/-! The explicit paired-column projector commutes with the standard
quaternionic anti-linear structure for every column, without assuming it
already lies in the compact-symplectic orbit. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnQuaternionic

open Matrix CompactSymplecticProjectorFirstColumn
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

theorem columnProjector_quaternionic (n : ℕ) (v : I n → ℂ) :
    columnProjector n v * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * (columnProjector n v).map star := by
  classical
  ext i j
  cases i with
  | inl a =>
    cases j with
    | inl b =>
      simp [columnProjector, pairedColumn, CompactSymplecticHaar.standardJ,
        Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
    | inr b =>
      simp [columnProjector, pairedColumn, CompactSymplecticHaar.standardJ,
        Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
      ring
  | inr a =>
    cases j with
    | inl b =>
      simp [columnProjector, pairedColumn, CompactSymplecticHaar.standardJ,
        Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
      ring
    | inr b =>
      simp [columnProjector, pairedColumn, CompactSymplecticHaar.standardJ,
        Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnQuaternionic
