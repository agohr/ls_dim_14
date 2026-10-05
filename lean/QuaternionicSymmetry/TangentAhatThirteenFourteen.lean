import QuaternionicSymmetry.AhatCoefficientPolynomialsSix
import QuaternionicSymmetry.TangentAhatCharacterDensity

/-! The genuine tangent A-hat formal exponential and the virtual character
convolution agree with the printed dimension-13/14 polynomials. -/
namespace QuaternionicSymmetry.TangentAhatThirteenFourteen
open MvPolynomial Characters FormalExponentialCoefficients
open TangentAhatCharacterDensity AhatCoefficientPolynomialsSix
noncomputable section
set_option maxHeartbeats 1500000
variable {R : Type} [CommRing R] [Algebra ℚ R]

private theorem coefficient_eval (n : ℕ) (u : R) (t : ℕ → R) (j : Fin 7) :
    tangentAhatCoefficient t j.val =
      aeval (RecoveredLogAhatSix.standardValues n u t)
        (DimensionThirteenFourteenDensity.Aext6 n (fun _ => 0) j.val) := by
  fin_cases j
  · simp [tangentAhatCoefficient, coefficient_zero,
      DimensionThirteenFourteenDensity.Aext6]
  · change tangentAhatCoefficient t 1 = aeval _
      (DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.a1 n))
    have h := AhatCoefficientPolynomials.coefficient_recovered n u t ⟨1, by decide⟩
    change tangentAhatCoefficient t 1 =
      aeval (RecoveredLogAhat.standardValues n u t) (DimensionElevenTwelveDensity.a1 n) at h
    exact h.trans (aeval_lift n u t _).symm
  · change tangentAhatCoefficient t 2 = aeval _
      (DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.a2 n))
    have h := AhatCoefficientPolynomials.coefficient_recovered n u t ⟨2, by decide⟩
    change tangentAhatCoefficient t 2 =
      aeval (RecoveredLogAhat.standardValues n u t) (DimensionElevenTwelveDensity.a2 n) at h
    exact h.trans (aeval_lift n u t _).symm
  · change tangentAhatCoefficient t 3 = aeval _
      (DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.a3 n))
    have h := AhatCoefficientPolynomials.coefficient_recovered n u t ⟨3, by decide⟩
    change tangentAhatCoefficient t 3 =
      aeval (RecoveredLogAhat.standardValues n u t) (DimensionElevenTwelveDensity.a3 n) at h
    exact h.trans (aeval_lift n u t _).symm
  · change tangentAhatCoefficient t 4 = aeval _
      (DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.a4 n))
    have h := AhatCoefficientPolynomials.coefficient_recovered n u t ⟨4, by decide⟩
    change tangentAhatCoefficient t 4 =
      aeval (RecoveredLogAhat.standardValues n u t) (DimensionElevenTwelveDensity.a4 n) at h
    exact h.trans (aeval_lift n u t _).symm
  · change tangentAhatCoefficient t 5 = aeval _
      (DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.a5 n))
    have h := AhatCoefficientPolynomials.coefficient_recovered n u t ⟨5, by decide⟩
    change tangentAhatCoefficient t 5 =
      aeval (RecoveredLogAhat.standardValues n u t) (DimensionElevenTwelveDensity.a5 n) at h
    exact h.trans (aeval_lift n u t _).symm
  · simpa only [tangentAhatCoefficient, DimensionThirteenFourteenDensity.Aext6]
      using coefficient_recovered_six n u t

private theorem characterDensity_eq_convolution (n : ℕ) (u : R) (t : ℕ → R)
    (hvanish : ∀ j, 7 ≤ j → j < n+1 →
      Characters.taylorCoefficient (n-j) (Characters.virtual n) = 0) :
    characterDensity n u t (virtual n) =
      aeval (RecoveredLogAhatSix.standardValues n u t)
        (DimensionThirteenFourteenDensity.characterConvolution n (fun _ => 0)) := by
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    DimensionThirteenFourteenDensity.characterConvolution, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hj7 : j < 7
  · have hc := coefficient_eval n u t ⟨j, hj7⟩
    simp only [map_mul, map_pow, aeval_C]
    rw [← hc]
    simp only [DimensionThirteenFourteenDensity.u, aeval_X]
    change _ = algebraMap ℚ R _ * u ^ (n-j) * tangentAhatCoefficient t j
    ring
  · have hz := hvanish j (by omega) (Finset.mem_range.mp hj)
    simp [hz]

theorem characterDensity_13 (u : R) (t : ℕ → R) :
    characterDensity 13 u t (virtual 13) =
      aeval (RecoveredLogAhatSix.standardValues 13 u t)
        DimensionThirteenFourteenDensity.density13 := by
  rw [characterDensity_eq_convolution 13 u t (by
    intro j hj hj13
    exact HigherCharacters.taylor_thirteen_below_7 (13-j) (by omega)),
    DimensionThirteenFourteenDensity.characterConvolution13]

theorem characterDensity_14 (u : R) (t : ℕ → R) :
    characterDensity 14 u t (virtual 14) =
      aeval (RecoveredLogAhatSix.standardValues 14 u t)
        DimensionThirteenFourteenDensity.density14 := by
  rw [characterDensity_eq_convolution 14 u t (by
    intro j hj hj14
    exact HigherCharacters.taylor_fourteen_below_8 (14-j) (by omega)),
    DimensionThirteenFourteenDensity.characterConvolution14]

end
end QuaternionicSymmetry.TangentAhatThirteenFourteen
