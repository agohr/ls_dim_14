import QuaternionicSymmetry.CompactSymplecticProjectorPeirceQuaternionic
import QuaternionicSymmetry.ProjectorPeirceConjugation

/-! Hermitianity, the linearized projector equation, and quaternionic
intertwining are transported by genuine unitary quaternionic conjugation. -/

namespace QuaternionicSymmetry.ProjectorQuaternionicConjugationConstraints

open Matrix
open scoped Matrix.Norms.Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem conjugation_hermitian (U A : Matrix ι ι ℂ)
    (hA : Aᴴ = A) :
    (U * A * Uᴴ)ᴴ = U * A * Uᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA]
  simp only [Matrix.mul_assoc]

theorem conjugation_tangent (U V P A : Matrix ι ι ℂ)
    (hVU : V * U = 1) (hA : P * A + A * P = A) :
    (U * P * V) * (U * A * V) +
      (U * A * V) * (U * P * V) = U * A * V := by
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc V U, hVU, one_mul]
  rw [← Matrix.mul_assoc P A V, ← Matrix.mul_assoc A P V,
    ← mul_add, ← add_mul, hA]

theorem conjugation_quaternionic
    (J U V A : Matrix ι ι ℂ)
    (hU : U * J = J * U.map star)
    (hV : V * J = J * V.map star)
    (hA : A * J = J * A.map star) :
    (U * A * V) * J = J * (U * A * V).map star := by
  calc
    U * A * V * J = U * A * (V * J) := by simp only [Matrix.mul_assoc]
    _ = U * A * (J * V.map star) := by rw [hV]
    _ = U * (A * J) * V.map star := by simp only [Matrix.mul_assoc]
    _ = U * (J * A.map star) * V.map star := by rw [hA]
    _ = (U * J) * (A.map star * V.map star) := by simp only [Matrix.mul_assoc]
    _ = (J * U.map star) * (A.map star * V.map star) := by rw [hU]
    _ = J * (U.map star * A.map star * V.map star) := by simp only [Matrix.mul_assoc]
    _ = J * (U * A * V).map star := by
      change J * (U.map (starRingEnd ℂ) * A.map (starRingEnd ℂ) *
          V.map (starRingEnd ℂ)) =
        J * (U * A * V).map (starRingEnd ℂ)
      rw [Matrix.map_mul, Matrix.map_mul]

end
end QuaternionicSymmetry.ProjectorQuaternionicConjugationConstraints
