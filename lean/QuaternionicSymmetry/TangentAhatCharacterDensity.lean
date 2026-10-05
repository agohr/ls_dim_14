import QuaternionicSymmetry.AhatCoefficientPolynomials

/-! The full formal A-hat/character convolution expressed directly in
normalized tangent half traces. Higher A-hat coefficients are retained;
the checked virtual characters eliminate them in dimensions eleven and twelve. -/
namespace QuaternionicSymmetry.TangentAhatCharacterDensity
open MvPolynomial Characters FormalExponentialCoefficients
open AhatCoefficientPolynomials RecoveredLogAhat
noncomputable section
variable {R : Type} [CommRing R] [Algebra ℚ R]

def tangentAhatCoefficient (t : ℕ → R) (j : ℕ) : R :=
  coefficient (fun m => algebraMap ℚ R (LogAhat.ell m) * t m) j

def characterDensity (n : ℕ) (u : R) (t : ℕ → R) :
    LaurentPolynomial ℚ →ₗ[ℚ] R where
  toFun p := ∑ j ∈ Finset.range (n+1),
    algebraMap ℚ R (taylorCoefficient (n-j) p) * u^(n-j) * tangentAhatCoefficient t j
  map_add' p q := by
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  map_smul' q p := by
    simp only [map_smul, smul_eq_mul, map_mul, RingHom.id_apply]
    simp only [Algebra.smul_def, Finset.mul_sum, mul_assoc]

theorem characterDensity_11 (u : R) (t : ℕ → R) :
    characterDensity 11 u t (virtual 11) =
      aeval (standardValues 11 u t) DimensionElevenTwelveDensity.density11 := by
  have h := HigherCharacters.taylor_eleven
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 11 u t ⟨0, by decide⟩]
  rw [coefficient_recovered 11 u t ⟨1, by decide⟩]
  rw [coefficient_recovered 11 u t ⟨2, by decide⟩]
  rw [coefficient_recovered 11 u t ⟨3, by decide⟩]
  rw [coefficient_recovered 11 u t ⟨4, by decide⟩]
  rw [coefficient_recovered 11 u t ⟨5, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.density11,
    DimensionElevenTwelveDensity.u, map_add, map_mul, map_pow, aeval_C, aeval_X]
  simp only [show standardValues 11 u t 0 = u from rfl, Nat.cast_ofNat]
  ac_rfl

theorem characterDensity_12 (u : R) (t : ℕ → R) :
    characterDensity 12 u t (virtual 12) =
      aeval (standardValues 12 u t) DimensionElevenTwelveDensity.density12 := by
  have h := HigherCharacters.taylor_twelve
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 12 u t ⟨0, by decide⟩]
  rw [coefficient_recovered 12 u t ⟨1, by decide⟩]
  rw [coefficient_recovered 12 u t ⟨2, by decide⟩]
  rw [coefficient_recovered 12 u t ⟨3, by decide⟩]
  rw [coefficient_recovered 12 u t ⟨4, by decide⟩]
  rw [coefficient_recovered 12 u t ⟨5, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.density12,
    DimensionElevenTwelveDensity.u, map_add, map_mul, map_pow, aeval_C, aeval_X]
  simp only [show standardValues 12 u t 0 = u from rfl, Nat.cast_ofNat]
  ac_rfl

end
end QuaternionicSymmetry.TangentAhatCharacterDensity
