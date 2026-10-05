import QuaternionicSymmetry.ProjectorPeirceTangentProjection

/-! Algebraic covariance of the ambient Peirce tangent projection under
an invertible matrix conjugation; later specialized to the actual Sp orbit. -/

namespace QuaternionicSymmetry.ProjectorPeirceConjugation

open ProjectorPeirceTangentProjection
noncomputable section

variable {A : Type*} [Ring A]

theorem tangentPart_conjugation (U V P X : A) (hVU : V * U = 1) :
    tangentPart (U * P * V) (U * X * V) =
      U * tangentPart P X * V := by
  simp only [tangentPart, two_nsmul, mul_add, add_mul, mul_sub, sub_mul]
  simp only [mul_assoc, ← mul_assoc V U, hVU, one_mul]

end
end QuaternionicSymmetry.ProjectorPeirceConjugation
