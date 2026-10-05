import QuaternionicSymmetry.CompactSymplecticProjectiveQuotient

/-! The actual conjugation orbit of the first quaternionic-coordinate projector.
This is a matrix-valued map on the compact symplectic group. Descent to the
coset carrier and identification with quaternionic projective space are
separate statements, not assumptions here. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorOrbit

open Matrix CompactSymplecticProjectiveQuotient
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Conjugation of the first-pair orthogonal projector by an actual compact
symplectic matrix. -/
def orbitProjector (n : ℕ) (u : CompactSymplecticHaar.Group (n + 1)) :
    Matrix (Fin (n + 1) ⊕ Fin (n + 1))
      (Fin (n + 1) ⊕ Fin (n + 1)) ℂ :=
  (u.1 : Matrix _ _ ℂ) * firstPairProjector n * (u.1 : Matrix _ _ ℂ)ᴴ

/-- The unitary adjoint in the orbit formula is the actual inverse matrix. -/
theorem orbitProjector_eq_mul_inverse (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    orbitProjector n u =
      (u.1 : Matrix _ _ ℂ) * firstPairProjector n *
        ((u⁻¹).1 : Matrix _ _ ℂ) := by
  unfold orbitProjector
  congr 1

/-- The projector orbit is continuous in the ambient complex matrix space. -/
theorem continuous_orbitProjector (n : ℕ) :
    Continuous (orbitProjector n) := by
  unfold orbitProjector
  exact ((continuous_subtype_val.comp continuous_subtype_val).mul continuous_const).mul
    (continuous_subtype_val.comp continuous_subtype_val).matrix_conjTranspose

/-- Every conjugate remains self-adjoint. -/
theorem orbitProjector_selfAdjoint (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    (orbitProjector n u)ᴴ = orbitProjector n u := by
  simp [orbitProjector, Matrix.conjTranspose_mul,
    firstPairProjector_selfAdjoint, mul_assoc]

/-- Every conjugate remains idempotent. -/
theorem orbitProjector_idempotent (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    orbitProjector n u * orbitProjector n u = orbitProjector n u := by
  have hU : (u.1.1 : Matrix _ _ ℂ)ᴴ * (u.1.1 : Matrix _ _ ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self u.1
  simp only [orbitProjector]
  calc
    _ = (u.1 : Matrix _ _ ℂ) *
        (firstPairProjector n * ((u.1 : Matrix _ _ ℂ)ᴴ * (u.1 : Matrix _ _ ℂ))) *
        firstPairProjector n * (u.1 : Matrix _ _ ℂ)ᴴ := by simp [mul_assoc]
    _ = _ := by
      rw [hU, mul_one]
      calc
        _ = (u.1 : Matrix _ _ ℂ) *
            (firstPairProjector n * firstPairProjector n) *
            (u.1 : Matrix _ _ ℂ)ᴴ := by simp only [mul_assoc]
        _ = _ := by rw [firstPairProjector_idempotent]

end
end QuaternionicSymmetry.CompactSymplecticProjectorOrbit
