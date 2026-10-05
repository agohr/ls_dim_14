import QuaternionicSymmetry.CompactSymplecticProjectorPeirceOrthogonal
import QuaternionicSymmetry.CompactSymplecticProjectorTangentConstraints

/-! The Peirce tangent projection preserves the actual quaternionic-
Hermitian real ambient matrix subspace. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorPeirceQuaternionic

open Matrix
open ProjectorPeirceTangentProjection
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem tangentPart_hermitian (n : ℕ) (P A : Mat n)
    (hP : Pᴴ = P) (hA : Aᴴ = A) :
    (tangentPart P A)ᴴ = tangentPart P A := by
  simp only [tangentPart, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nsmul, hP, hA]
  simp only [Matrix.mul_assoc]
  abel

private theorem intertwiner_mul (n : ℕ) (J A B : Mat n)
    (hA : A * J = J * A.map star)
    (hB : B * J = J * B.map star) :
    (A * B) * J = J * (A * B).map star := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA,
    Matrix.mul_assoc]
  change J * (A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ)) =
    J * (A * B).map (starRingEnd ℂ)
  rw [Matrix.map_mul]

theorem tangentPart_quaternionic (n : ℕ) (J P A : Mat n)
    (hP : P * J = J * P.map star)
    (hA : A * J = J * A.map star) :
    tangentPart P A * J = J * (tangentPart P A).map star := by
  have hPA := intertwiner_mul n J P A hP hA
  have hAP := intertwiner_mul n J A P hA hP
  have hPAP := intertwiner_mul n J (P * A) P hPA hP
  simp only [tangentPart, two_nsmul, sub_mul, add_mul,
    Matrix.map_sub, Matrix.map_add]
  rw [hPA, hAP, hPAP]
  change J * (P * A).map (starRingEnd ℂ) +
      J * (A * P).map (starRingEnd ℂ) -
        (J * (P * A * P).map (starRingEnd ℂ) +
          J * (P * A * P).map (starRingEnd ℂ)) =
    J * (P * A + A * P - (P * A * P + P * A * P)).map (starRingEnd ℂ)
  rw [Matrix.map_sub, Matrix.map_add, Matrix.map_add] <;> simp
  simp only [mul_add, mul_sub]

end
end QuaternionicSymmetry.CompactSymplecticProjectorPeirceQuaternionic
