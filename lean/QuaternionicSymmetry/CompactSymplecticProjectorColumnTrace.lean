import QuaternionicSymmetry.CompactSymplecticProjectorColumnPhaseNormalize

/-! The trace of a paired-column projector records twice the squared norm of
its defining complex column. This converts phase-invariant projector equality
into unit-norm preservation without a separate quaternionic norm calculus. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnTrace

open Matrix CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnAlgebra
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

theorem columnProjector_trace (n : ℕ) (v : I n → ℂ) :
    Matrix.trace (columnProjector n v) =
      2 * ((fun i => star (v i)) ⬝ᵥ v) := by
  classical
  calc
    Matrix.trace (columnProjector n v) =
        ((fun i => star (v i)) ⬝ᵥ v) +
          ((fun i => star (pairedColumn n v i)) ⬝ᵥ pairedColumn n v) := by
            simp [Matrix.trace, columnProjector, dotProduct,
              Finset.sum_add_distrib, mul_comm]
    _ = 2 * ((fun i => star (v i)) ⬝ᵥ v) := by
      rw [pairedColumn_norm_sq]
      ring

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnTrace
