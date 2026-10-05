import QuaternionicSymmetry.RecoveredLogAhat
import QuaternionicSymmetry.FormalExponentialCoefficients

/-! The printed A-hat polynomials through weight five satisfy the full
formal-exponential recurrence, without assumptions on higher coefficients. -/
namespace QuaternionicSymmetry.AhatCoefficientPolynomials
open MvPolynomial FormalExponentialCoefficients
noncomputable section
set_option maxHeartbeats 2000000
abbrev P := DimensionElevenTwelveDensity.P

def logarithmicSequence (n : ℕ) : ℕ → P
  | 1 => DimensionElevenTwelveDensity.b1 n
  | 2 => DimensionElevenTwelveDensity.b2 n
  | 3 => DimensionElevenTwelveDensity.b3 n
  | 4 => DimensionElevenTwelveDensity.b4 n
  | 5 => DimensionElevenTwelveDensity.b5 n
  | _ => 0

def coefficientPolynomial (n : ℕ) : ℕ → P
  | 0 => DimensionElevenTwelveDensity.a0
  | 1 => DimensionElevenTwelveDensity.a1 n
  | 2 => DimensionElevenTwelveDensity.a2 n
  | 3 => DimensionElevenTwelveDensity.a3 n
  | 4 => DimensionElevenTwelveDensity.a4 n
  | 5 => DimensionElevenTwelveDensity.a5 n
  | _ => 0

theorem logarithmicSequence_eq (n : ℕ) (j : Fin 5) :
    logarithmicSequence n (j.val+1) = RecoveredLogAhat.logarithmicPolynomial n j := by
  fin_cases j <;> rfl

theorem coefficient_polynomial (n : ℕ) (j : Fin 6) :
    coefficient (logarithmicSequence n) j.val = coefficientPolynomial n j.val := by
  apply MvPolynomial.funext
  intro v
  change (eval₂Hom (RingHom.id ℚ) v) (coefficient _ _) = _
  rw [map_coefficient]
  fin_cases j <;>
    simp [coefficient, coefficientPolynomial, logarithmicSequence,
      Fin.sum_univ_succ,
      DimensionElevenTwelveDensity.a0, DimensionElevenTwelveDensity.a1,
      DimensionElevenTwelveDensity.a2, DimensionElevenTwelveDensity.a3,
      DimensionElevenTwelveDensity.a4, DimensionElevenTwelveDensity.a5,
      DimensionElevenTwelveDensity.b1, DimensionElevenTwelveDensity.b2,
      DimensionElevenTwelveDensity.b3, DimensionElevenTwelveDensity.b4,
      DimensionElevenTwelveDensity.b5, DimensionElevenTwelveDensity.old,
      AlgebraCertificates.evaluate, AlgebraCertificates.A₁,
      AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄,
      AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃,
      AlgebraCertificates.b₄, AlgebraCertificates.c, AlgebraCertificates.U,
      AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃,
      AlgebraCertificates.Z₄, DimensionElevenTwelveDensity.u,
      DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
      DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4,
      DimensionElevenTwelveDensity.p5] <;> ring


variable {R : Type} [CommRing R] [Algebra ℚ R]

theorem coefficient_recovered (n : ℕ) (u : R) (t : ℕ → R) (j : Fin 6) :
    coefficient (fun m => algebraMap ℚ R (LogAhat.ell m) * t m) j.val =
      aeval (RecoveredLogAhat.standardValues n u t) (coefficientPolynomial n j.val) := by
  rw [← coefficient_polynomial n j]
  change coefficient _ _ =
    (aeval (RecoveredLogAhat.standardValues n u t)).toRingHom
      (coefficient (logarithmicSequence n) j.val)
  rw [map_coefficient]
  apply coefficient_congr
  intro m hm hmj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hk : k < 5 := by omega
  rw [logarithmicSequence_eq n ⟨k, hk⟩]
  exact (RecoveredLogAhat.evaluated_logarithmic n u t ⟨k, hk⟩).symm

end
end QuaternionicSymmetry.AhatCoefficientPolynomials
