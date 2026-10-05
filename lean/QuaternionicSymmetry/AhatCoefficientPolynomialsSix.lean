import QuaternionicSymmetry.RecoveredLogAhatSix
import QuaternionicSymmetry.AhatCoefficientPolynomials

/-! The sixth formal A-hat coefficient is the exponential of the six
logarithmic coefficients in the enlarged seven-variable ring. -/
namespace QuaternionicSymmetry.AhatCoefficientPolynomialsSix
open MvPolynomial FormalExponentialCoefficients
noncomputable section
set_option maxHeartbeats 1000000

abbrev P := DimensionThirteenFourteenDensity.P

def logarithmicSequence (n : ℕ) : ℕ → P
  | 1 => DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.b1 n)
  | 2 => DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.b2 n)
  | 3 => DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.b3 n)
  | 4 => DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.b4 n)
  | 5 => DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.b5 n)
  | 6 => DimensionThirteenFourteenDensity.b6 n
  | _ => 0

theorem logarithmicSequence_lower (n : ℕ) (j : Fin 6) :
    logarithmicSequence n j.val =
      DimensionThirteenFourteenDensity.lift
        (AhatCoefficientPolynomials.logarithmicSequence n j.val) := by
  fin_cases j <;> rfl

theorem coefficient_lower (n : ℕ) (j : Fin 6) :
    coefficient (logarithmicSequence n) j.val =
      DimensionThirteenFourteenDensity.lift
        (AhatCoefficientPolynomials.coefficientPolynomial n j.val) := by
  have h := congrArg DimensionThirteenFourteenDensity.lift
    (AhatCoefficientPolynomials.coefficient_polynomial n j)
  change (DimensionThirteenFourteenDensity.lift.toRingHom)
    (coefficient (AhatCoefficientPolynomials.logarithmicSequence n) j.val) = _ at h
  rw [map_coefficient] at h
  rw [← h]
  apply coefficient_congr
  intro m hm hmj
  exact logarithmicSequence_lower n ⟨m, by omega⟩

theorem coefficient_six (n : ℕ) :
    coefficient (logarithmicSequence n) 6 =
      DimensionThirteenFourteenDensity.a6 n := by
  have h6 : (6 : P) * coefficient (logarithmicSequence n) 6 =
      6 * DimensionThirteenFourteenDensity.a6 n := by
    have hrec := FormalExponentialCoefficients.recurrence
      (logarithmicSequence n) 5
    norm_num only [Nat.reduceAdd] at hrec
    rw [hrec, DimensionThirteenFourteenDensity.a6_recurrence]
    simp [Fin.sum_univ_succ, logarithmicSequence]
    rw [coefficient_lower n ⟨0, by decide⟩,
      coefficient_lower n ⟨1, by decide⟩,
      coefficient_lower n ⟨2, by decide⟩,
      coefficient_lower n ⟨3, by decide⟩,
      coefficient_lower n ⟨4, by decide⟩,
      coefficient_lower n ⟨5, by decide⟩]
    simp only [AhatCoefficientPolynomials.coefficientPolynomial,
      DimensionElevenTwelveDensity.a0, map_one, mul_one]
    ring
  exact mul_left_cancel₀ (by norm_num : (6 : P) ≠ 0) h6

variable {R : Type} [CommRing R] [Algebra ℚ R]

theorem aeval_lift (n : ℕ) (u : R) (t : ℕ → R)
    (p : DimensionElevenTwelveDensity.P) :
    aeval (RecoveredLogAhatSix.standardValues n u t)
      (DimensionThirteenFourteenDensity.lift p) =
    aeval (RecoveredLogAhat.standardValues n u t) p := by
  change aeval _ (aeval _ p) = _
  rw [comp_aeval_apply]
  have hfun : (fun i => (aeval (RecoveredLogAhatSix.standardValues n u t))
      (![DimensionThirteenFourteenDensity.u, DimensionThirteenFourteenDensity.p1,
        DimensionThirteenFourteenDensity.p2, DimensionThirteenFourteenDensity.p3,
        DimensionThirteenFourteenDensity.p4, DimensionThirteenFourteenDensity.p5] i)) =
      RecoveredLogAhat.standardValues n u t := by
    funext i
    fin_cases i <;>
      simp [RecoveredLogAhatSix.standardValues,
        RecoveredLogAhat.standardValues, DimensionThirteenFourteenDensity.u,
        DimensionThirteenFourteenDensity.p1,
        DimensionThirteenFourteenDensity.p2,
        DimensionThirteenFourteenDensity.p3,
        DimensionThirteenFourteenDensity.p4,
        DimensionThirteenFourteenDensity.p5]
  rw [hfun]

theorem evaluated_logarithmic_lower (n : ℕ) (u : R) (t : ℕ → R)
    (j : Fin 5) :
    aeval (RecoveredLogAhatSix.standardValues n u t)
        (logarithmicSequence n (j.val + 1)) =
      algebraMap ℚ R (LogAhat.ell (j.val + 1)) * t (j.val + 1) := by
  rw [show logarithmicSequence n (j.val+1) =
    DimensionThirteenFourteenDensity.lift
      (RecoveredLogAhat.logarithmicPolynomial n j) by fin_cases j <;> rfl,
    aeval_lift]
  exact RecoveredLogAhat.evaluated_logarithmic n u t j

theorem evaluated_logarithmic_six (n : ℕ) (u : R) (t : ℕ → R) :
    aeval (RecoveredLogAhatSix.standardValues n u t)
        (logarithmicSequence n 6) =
      algebraMap ℚ R (LogAhat.ell 6) * t 6 := by
  exact RecoveredLogAhatSix.evaluated_logarithmic_six n u t

theorem coefficient_recovered_six (n : ℕ) (u : R) (t : ℕ → R) :
    coefficient (fun m => algebraMap ℚ R (LogAhat.ell m) * t m) 6 =
      aeval (RecoveredLogAhatSix.standardValues n u t)
        (DimensionThirteenFourteenDensity.a6 n) := by
  rw [← coefficient_six n]
  change coefficient _ _ =
    (aeval (RecoveredLogAhatSix.standardValues n u t)).toRingHom
      (coefficient (logarithmicSequence n) 6)
  rw [map_coefficient]
  apply coefficient_congr
  intro m hm hm6
  rcases lt_or_eq_of_le hm6 with hlt | heq
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    exact (evaluated_logarithmic_lower n u t ⟨j, by omega⟩).symm
  · subst m
    exact (evaluated_logarithmic_six n u t).symm

end
end QuaternionicSymmetry.AhatCoefficientPolynomialsSix
