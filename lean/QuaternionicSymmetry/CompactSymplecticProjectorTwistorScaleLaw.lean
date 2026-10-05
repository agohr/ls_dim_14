import QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberLaw

/-! Exact complex scaling law for the paired-column rank-two projector.
It is the algebraic descent step for the normalized map from complex
projective lines to quaternionic lines. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorScaleLaw

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnAlgebra

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

theorem columnProjector_smul (n : ℕ) (t : ℂ) (v : I n → ℂ) :
    columnProjector n (t • v) = (star t * t) • columnProjector n v := by
  ext i j
  simp only [columnProjector, pairedColumn_smul, Pi.smul_apply,
    Matrix.smul_apply, smul_eq_mul, star_mul, star_star]
  ring

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorScaleLaw
