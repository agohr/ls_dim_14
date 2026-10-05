import QuaternionicSymmetry.CompactSymplecticProjectorColumnUnit

/-! A unit complex column and its forced quaternionic mate span an actual
rank-two orthogonal projector, proved by the four outer-product terms. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnIdempotent

open Matrix CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnAlgebra
open CompactSymplecticProjectorColumnUnit
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

theorem columnProjector_eq_outer_sum (n : ℕ) (v : I n → ℂ) :
    columnProjector n v =
      Matrix.vecMulVec v (fun i => star (v i)) +
        Matrix.vecMulVec (pairedColumn n v) (fun i => star (pairedColumn n v i)) := by
  ext i j
  rfl

theorem columnProjector_selfAdjoint (n : ℕ) (v : I n → ℂ) :
    (columnProjector n v)ᴴ = columnProjector n v := by
  ext i j
  simp [columnProjector, mul_comm]

theorem columnProjector_idempotent_of_dot (n : ℕ) (v : I n → ℂ)
    (hv : (fun i => star (v i)) ⬝ᵥ v = 1) :
    columnProjector n v * columnProjector n v = columnProjector n v := by
  let w := pairedColumn n v
  have hw : (fun i => star (w i)) ⬝ᵥ w = 1 := by
    simpa only [w] using (pairedColumn_norm_sq n v).trans hv
  have hvw : (fun i => star (v i)) ⬝ᵥ w = 0 := pairedColumn_orthogonal n v
  have hwv : (fun i => star (w i)) ⬝ᵥ v = 0 := pairedColumn_orthogonal_rev n v
  rw [columnProjector_eq_outer_sum]
  change (Matrix.vecMulVec v (fun i => star (v i)) +
    Matrix.vecMulVec w (fun i => star (w i))) *
    (Matrix.vecMulVec v (fun i => star (v i)) +
    Matrix.vecMulVec w (fun i => star (w i))) = _
  simp only [add_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec,
    hv, hw, hvw, hwv, one_smul, zero_smul, Matrix.vecMulVec_zero]
  abel

theorem unit_columnProjector_idempotent (n : ℕ)
    (v : Metric.sphere (0 : EuclideanSpace ℂ (I n)) 1) :
    columnProjector n ((EuclideanSpace.equiv (I n) ℂ) v.1) *
      columnProjector n ((EuclideanSpace.equiv (I n) ℂ) v.1) =
        columnProjector n ((EuclideanSpace.equiv (I n) ℂ) v.1) := by
  apply columnProjector_idempotent_of_dot
  exact unit_column_dot_self n v

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnIdempotent
