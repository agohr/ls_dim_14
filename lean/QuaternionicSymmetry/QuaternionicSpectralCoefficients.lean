import QuaternionicSymmetry.QuaternionicPencilPolynomial
import QuaternionicSymmetry.GaussianAffineCoefficients
import QuaternionicSymmetry.GaussianRadialProduct
import QuaternionicSymmetry.SpectralNormalization

/-! Coefficient comparison for the actual quaternionic block pencil. -/

namespace QuaternionicSymmetry.QuaternionicSpectralCoefficients

open scoped BigOperators
open QuaternionicPencilPolynomial GaussianPolynomialExpectation

noncomputable section

variable {β : Type*} [Fintype β] [DecidableEq β]

def fundamental : Eev β := ∑ i : Fin 3, omega i ^ 2

def spectralWeight (lam : β → ℝ) (k : ℕ) : ℝ :=
  GaussianRadialProduct.elementary Finset.univ (fun j => lam j ^ 2) k

omit [DecidableEq β] in
theorem spectralWeight_nonneg (lam : β → ℝ) (k : ℕ) : 0 ≤ spectralWeight lam k :=
  GaussianRadialProduct.elementary_sq_nonneg _ _ _

omit [DecidableEq β] in
@[simp] theorem spectralWeight_zero (lam : β → ℝ) : spectralWeight lam 0 = 1 := by
  simp [spectralWeight, GaussianRadialProduct.elementary]

theorem coefficient_relation (lam : β → ℝ) (k : ℕ) (hk : k ≤ Fintype.card β) :
    momentScalar (Fintype.card β) k •
      (theta lam ^ (2 * k) * (fundamental : Eev β) ^ (Fintype.card β - k)) =
    ((-1 : ℝ) ^ k * radialScalar (Fintype.card β) k * spectralWeight lam k) •
      (volume : Eev β) := by
  have h := congrArg (fun p : MvPolynomial (Fin 3) (Polynomial (Eev β)) =>
      (expectation p).coeff (2 * k)) (pencilPolynomial_top_power lam)
  dsimp only at h
  rw [pencilPolynomial, GaussianAffineCoefficients.coeff_expectation_affine
    _ _ _ _ (by omega)] at h
  rw [GaussianAffineMoments.expectation_C_mul, Polynomial.coeff_C_mul] at h
  have hc := GaussianRadialProduct.coeff_expectation_product_sq
    (S := Eev β) Finset.univ (fun j => algebraMap ℝ (Eev β) (lam j ^ 2)) k (by simpa using hk)
  change (expectation (coefficientPolynomial lam)).coeff (2 * k) = _ at hc
  rw [hc, GaussianRadialProduct.elementary_algebraMap] at h
  rw [show 2 * Fintype.card β - 2 * k = 2 * (Fintype.card β - k) by omega] at h
  simp only [GaussianMomentPolynomials.moment, Nat.mul_mod_right, ↓reduceIte,
    Nat.mul_div_cancel_left, Nat.ofNat_pos, Finset.card_univ] at h
  simpa only [momentScalar, radialScalar, spectralWeight, fundamental, Algebra.smul_def,
    map_mul, map_pow, map_neg, map_one, map_natCast, mul_assoc, mul_left_comm, mul_comm] using h

theorem signed_coefficient_relation (lam : β → ℝ) (k : ℕ) (hk : k ≤ Fintype.card β) :
    momentScalar (Fintype.card β) k •
      ((-(theta lam) ^ 2) ^ k * (fundamental : Eev β) ^ (Fintype.card β - k)) =
    (radialScalar (Fintype.card β) k * spectralWeight lam k) • (volume : Eev β) := by
  have hneg : (-(theta lam) ^ 2) ^ k = (-1 : ℝ) ^ k • theta lam ^ (2 * k) := by
    rw [← neg_one_smul ℝ ((theta lam) ^ 2), smul_pow, ← pow_mul]
  calc
    _ = (-1 : ℝ) ^ k • (momentScalar (Fintype.card β) k •
        (theta lam ^ (2 * k) * (fundamental : Eev β) ^ (Fintype.card β - k))) := by
      rw [hneg, smul_mul_assoc, smul_comm]
    _ = _ := by
      rw [coefficient_relation lam k hk, smul_smul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, ← pow_add, show k + k = 2 * k by omega,
        pow_mul, neg_one_sq, one_pow, one_mul]

theorem signed_mixed_nonneg_of_volume (lam : β → ℝ) (k : ℕ) (hk : k ≤ Fintype.card β)
    (L : Eev β →ₗ[ℝ] ℝ) (hvol : 0 ≤ L volume) :
    0 ≤ L ((-(theta lam) ^ 2) ^ k * (fundamental : Eev β) ^ (Fintype.card β - k)) := by
  have h := congrArg L (signed_coefficient_relation lam k hk)
  simp only [map_smul, smul_eq_mul] at h
  apply (mul_nonneg_iff_of_pos_left (momentScalar_pos _ _ hk)).mp
  rw [h]
  exact mul_nonneg (mul_nonneg (radialScalar_pos _ _).le (spectralWeight_nonneg lam k)) hvol

/-- The exact factorial coefficient in the spectral formula, in every dimension. -/
theorem signed_mixed_eq (lam : β → ℝ) (k : ℕ) (hk : k ≤ Fintype.card β) :
    (-(theta lam) ^ 2) ^ k * (fundamental : Eev β) ^ (Fintype.card β - k) =
      (((2 * k).factorial : ℝ) * ((2 * (Fintype.card β - k) + 1).factorial : ℝ) *
        spectralWeight lam k) • (volume : Eev β) := by
  have h := signed_coefficient_relation lam k hk
  rw [← scalar_normalization _ _ hk] at h
  have hi := congrArg (fun x : Eev β => (momentScalar (Fintype.card β) k)⁻¹ • x) h
  simpa only [smul_smul, ← mul_assoc, inv_mul_cancel₀ (momentScalar_pos _ _ hk).ne',
    one_smul, one_mul] using hi

theorem fundamental_top_power :
    (fundamental : Eev β) ^ Fintype.card β =
      ((2 * Fintype.card β + 1).factorial : ℝ) • (volume : Eev β) := by
  simpa only [Nat.mul_zero, pow_zero, one_mul, Nat.sub_zero, Nat.factorial_zero,
    Nat.cast_one, spectralWeight_zero, mul_one] using
    signed_mixed_eq (fun _ : β => 0) 0 (Nat.zero_le _)

theorem volume_eq_normalized_fundamental :
    (volume : Eev β) = ((2 * Fintype.card β + 1).factorial : ℝ)⁻¹ •
      (fundamental : Eev β) ^ Fintype.card β := by
  rw [fundamental_top_power, smul_smul, inv_mul_cancel₀ (by positivity :
    ((2 * Fintype.card β + 1).factorial : ℝ) ≠ 0), one_smul]

/-- Positivity can be normalized by the quaternionic fundamental form itself. -/
theorem signed_mixed_nonneg (lam : β → ℝ) (k : ℕ) (hk : k ≤ Fintype.card β)
    (L : Eev β →ₗ[ℝ] ℝ) (hfund : 0 ≤ L ((fundamental : Eev β) ^ Fintype.card β)) :
    0 ≤ L ((-(theta lam) ^ 2) ^ k * (fundamental : Eev β) ^ (Fintype.card β - k)) := by
  apply signed_mixed_nonneg_of_volume lam k hk L
  have h := congrArg L (coefficient_relation lam 0 (Nat.zero_le _))
  simp only [Nat.mul_zero, pow_zero, one_mul, Nat.sub_zero, spectralWeight_zero, mul_one,
    map_smul, smul_eq_mul] at h
  apply (mul_nonneg_iff_of_pos_left (radialScalar_pos (Fintype.card β) 0)).mp
  rw [← h]
  exact mul_nonneg (momentScalar_pos _ _ (Nat.zero_le _)).le hfund

theorem signed_mixed_map_nonneg {S : Type*} [CommRing S] [Algebra ℝ S]
    (F : Eev β →ₐ[ℝ] S) (lam : β → ℝ) (k : ℕ) (hk : k ≤ Fintype.card β)
    (L : S →ₗ[ℝ] ℝ) (hfund : 0 ≤ L (F fundamental ^ Fintype.card β)) :
    0 ≤ L ((-F (theta lam) ^ 2) ^ k * F fundamental ^ (Fintype.card β - k)) := by
  have h := signed_mixed_nonneg lam k hk (L.comp F.toLinearMap)
  have hf : 0 ≤ (L.comp F.toLinearMap) ((fundamental : Eev β) ^ Fintype.card β) := by
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow] using hfund
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, map_mul, map_neg] using h hf

theorem signed_mixed_eq_map {S : Type*} [CommRing S] [Algebra ℝ S]
    (F : Eev β →ₐ[ℝ] S) (lam : β → ℝ) (k : ℕ) (hk : k ≤ Fintype.card β) :
    (-F (theta lam) ^ 2) ^ k * F fundamental ^ (Fintype.card β - k) =
      (((2 * k).factorial : ℝ) * ((2 * (Fintype.card β - k) + 1).factorial : ℝ) *
        spectralWeight lam k) • F volume := by
  simpa only [map_mul, map_pow, map_neg, map_smul] using
    congrArg F (signed_mixed_eq lam k hk)

end
end QuaternionicSymmetry.QuaternionicSpectralCoefficients
