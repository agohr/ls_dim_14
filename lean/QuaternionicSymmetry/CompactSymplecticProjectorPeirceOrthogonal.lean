import QuaternionicSymmetry.CompactSymplecticProjectorPeirceTangent
import QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric

/-! The algebraic Peirce tangent projection of a Hermitian projector is
self-adjoint for the actual ambient Hilbert--Schmidt pairing. This is the
orthogonal-projection ingredient for an immersed-projector Gauss formula. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorPeirceOrthogonal

open Matrix
open CompactSymplecticProjectorAmbientMetric
open ProjectorPeirceTangentProjection
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem frobenius_left_mul_adjoint (n : ℕ) (P A B : Mat n)
    (hP : Pᴴ = P) :
    frobeniusPairing n (P * A) B = frobeniusPairing n A (P * B) := by
  simp only [frobeniusPairing, Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]

theorem frobenius_right_mul_adjoint (n : ℕ) (P A B : Mat n)
    (hP : Pᴴ = P) :
    frobeniusPairing n (A * P) B = frobeniusPairing n A (B * P) := by
  simp only [frobeniusPairing, Matrix.conjTranspose_mul, hP]
  rw [Matrix.mul_assoc P Aᴴ B, Matrix.trace_mul_comm P (Aᴴ * B)]
  simp only [Matrix.mul_assoc]

theorem tangentPart_frobenius_selfAdjoint (n : ℕ) (P A B : Mat n)
    (hP : Pᴴ = P) :
    frobeniusCLM n (tangentPart P A) B =
      frobeniusCLM n A (tangentPart P B) := by
  -- The two-sided term is self-adjoint by applying both one-sided laws.
  have htwoside : frobeniusPairing n (P * A * P) B =
      frobeniusPairing n A (P * B * P) := by
    calc
      _ = frobeniusPairing n (P * A) (B * P) :=
        frobenius_right_mul_adjoint n P (P * A) B hP
      _ = frobeniusPairing n A (P * (B * P)) :=
        frobenius_left_mul_adjoint n P A (B * P) hP
      _ = _ := by rw [Matrix.mul_assoc]
  simp only [tangentPart]
  simp only [map_sub, map_add, map_nsmul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply]
  simp only [frobeniusCLM_apply]
  rw [frobenius_left_mul_adjoint n P A B hP,
    frobenius_right_mul_adjoint n P A B hP, htwoside]

end
end QuaternionicSymmetry.CompactSymplecticProjectorPeirceOrthogonal
