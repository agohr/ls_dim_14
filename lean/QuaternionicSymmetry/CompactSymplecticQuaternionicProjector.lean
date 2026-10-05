import QuaternionicSymmetry.CompactSymplecticProjectorTrace

/-! The first-pair projector respects the standard quaternionic pairing
encoded by the alternating matrix `standardJ`. -/

namespace QuaternionicSymmetry.CompactSymplecticQuaternionicProjector

open Matrix CompactSymplecticProjectiveQuotient CompactSymplecticHaar
open scoped Matrix.Norms.Elementwise
noncomputable section

private def firstCoordinateProjector (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else 0)

/-- The paired projector consists of identical coordinate projectors on
the two complex halves. -/
theorem firstPairProjector_fromBlocks (n : ℕ) :
    firstPairProjector n =
      Matrix.fromBlocks (firstCoordinateProjector n) 0 0
        (firstCoordinateProjector n) := by
  classical
  ext (i | i) (j | j) <;>
    simp [firstPairProjector, firstCoordinateProjector,
      Matrix.fromBlocks, Matrix.diagonal_apply]

/-- The chosen two-complex-dimensional coordinate plane is an actual
quaternionic line: its orthogonal projector commutes with `standardJ`. -/
theorem firstPairProjector_commutes_standardJ (n : ℕ) :
    firstPairProjector n * standardJ (n + 1) =
      standardJ (n + 1) * firstPairProjector n := by
  rw [firstPairProjector_fromBlocks]
  simp [standardJ, Matrix.fromBlocks_multiply]

end
end QuaternionicSymmetry.CompactSymplecticQuaternionicProjector
