import QuaternionicSymmetry.OrbitalRankOneHC

/-!
# First rank-two coefficients of the symplectic odd determinant

The rank-two instance of the normalized determinant in
Forrester--Ipsen--Liu--Zhang, arXiv:1711.10691v1, Eq. (1.8), has prefactor
`(1! * 3! / 2²) * 2² = 6` when each determinant entry is written as a plain
`sinh` series.  We compare its low coefficients with the denominator and the
two rank-two Schur contributions.  These are formal identities over `ℚ`;
the source integral itself is not reconstructed here. -/

namespace QuaternionicSymmetry.OrbitalRankTwoHC

open PowerSeries OrbitalRankOneHC

noncomputable section

def sinhSeries : PowerSeries ℚ :=
  (PowerSeries.X : PowerSeries ℚ) * oddKernel

theorem coeff_sinhSeries (m : ℕ) :
    PowerSeries.coeff m sinhSeries =
      (1 - (-1 : ℚ) ^ m) / (2 * (Nat.factorial m : ℚ)) := by
  rw [sinhSeries, X_mul_oddKernel]
  simp [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  ring

/-- The rank-two source numerator after incorporating its normalized Haar
constant and the factors of two in `2 sinh`. -/
def normalizedOddNumerator (x₁ x₂ y₁ y₂ : ℚ) : PowerSeries ℚ :=
  PowerSeries.C (6 : ℚ) *
    (PowerSeries.rescale (x₁ * y₁) sinhSeries *
        PowerSeries.rescale (x₂ * y₂) sinhSeries -
      PowerSeries.rescale (x₁ * y₂) sinhSeries *
        PowerSeries.rescale (x₂ * y₁) sinhSeries)

def oddVandermondeProduct (x₁ x₂ y₁ y₂ : ℚ) : ℚ :=
  x₁ * x₂ * (x₂ ^ 2 - x₁ ^ 2) * y₁ * y₂ * (y₂ ^ 2 - y₁ ^ 2)

private def c (m : ℕ) : ℚ :=
  (1 - (-1 : ℚ) ^ m) / (2 * (Nat.factorial m : ℚ))

private theorem coeff_normalizedOddNumerator (x₁ x₂ y₁ y₂ : ℚ) (m : ℕ) :
    PowerSeries.coeff m (normalizedOddNumerator x₁ x₂ y₁ y₂) =
      6 * ∑ i ∈ Finset.range (m + 1), c i * c (m - i) *
        ((x₁ * y₁) ^ i * (x₂ * y₂) ^ (m - i) -
          (x₁ * y₂) ^ i * (x₂ * y₁) ^ (m - i)) := by
  unfold normalizedOddNumerator
  rw [PowerSeries.coeff_C_mul, map_sub]
  simp only [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_rescale, coeff_sinhSeries, c]
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coefficient_four (x₁ x₂ y₁ y₂ : ℚ) :
    PowerSeries.coeff 4 (normalizedOddNumerator x₁ x₂ y₁ y₂) =
      oddVandermondeProduct x₁ x₂ y₁ y₂ := by
  rw [coeff_normalizedOddNumerator]
  norm_num [c, oddVandermondeProduct, Finset.sum_range_succ]
  ring

/-- The first nonconstant type-C term has the ratio `3! / 5! = 1/20`
before the full-trace `4^1` rescaling. -/
theorem coefficient_six (x₁ x₂ y₁ y₂ : ℚ) :
    PowerSeries.coeff 6 (normalizedOddNumerator x₁ x₂ y₁ y₂) =
      oddVandermondeProduct x₁ x₂ y₁ y₂ *
        ((x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) / 20) := by
  rw [coeff_normalizedOddNumerator]
  norm_num [c, oddVandermondeProduct, Finset.sum_range_succ]
  ring

/-- At weight two, the two Schur pieces carry the respective factors
`3! / 7! = 1/840` and `(3! / 5!) * (1! / 3!) = 1/120`. -/
theorem coefficient_eight (x₁ x₂ y₁ y₂ : ℚ) :
    PowerSeries.coeff 8 (normalizedOddNumerator x₁ x₂ y₁ y₂) =
      oddVandermondeProduct x₁ x₂ y₁ y₂ *
        (((x₁ ^ 4 + x₁ ^ 2 * x₂ ^ 2 + x₂ ^ 4) *
              (y₁ ^ 4 + y₁ ^ 2 * y₂ ^ 2 + y₂ ^ 4) / 840) +
          (x₁ ^ 2 * x₂ ^ 2 * y₁ ^ 2 * y₂ ^ 2 / 120)) := by
  rw [coeff_normalizedOddNumerator]
  norm_num [c, oddVandermondeProduct, Finset.sum_range_succ]
  ring

/-- Spectral substitution for the two squared roots. -/
def rankTwoPowerSumEval (b₁ b₂ : ℚ) : FiniteTypeCSchurSix.P →ₐ[ℚ] ℚ :=
  MvPolynomial.aeval fun i => b₁ ^ (i.val + 1) + b₂ ^ (i.val + 1)

/-- Cross-multiplied weight-one bridge to the existing type-C orbital. -/
theorem orbital_two_first_hc (x₁ x₂ : ℕ) (y₁ y₂ : ℚ) :
    oddVandermondeProduct (x₁ : ℚ) x₂ y₁ y₂ *
      rankTwoPowerSumEval (y₁ ^ 2) (y₂ ^ 2)
        (FiniteTypeCSchurSix.orbital 2 1 [x₁ ^ 2, x₂ ^ 2]) =
      4 * PowerSeries.coeff 6
        (normalizedOddNumerator (x₁ : ℚ) x₂ y₁ y₂) := by
  rw [coefficient_six]
  simp [rankTwoPowerSumEval, FiniteTypeCSchurSix.orbital,
    FiniteTypeCSchurSix.partitions, QuarticOrbitalEleven.factorialRho,
    FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.powerSum, FiniteTypeCSchurSix.h1,
    FiniteTypeCSchurSix.p1]
  ring

/-- Cross-multiplied weight-two bridge.  This checks the separate `[2]`
and `[1,1]` Schur coefficients against the finite orbital interface. -/
theorem orbital_two_second_hc (x₁ x₂ : ℕ) (y₁ y₂ : ℚ) :
    oddVandermondeProduct (x₁ : ℚ) x₂ y₁ y₂ *
      rankTwoPowerSumEval (y₁ ^ 2) (y₂ ^ 2)
        (FiniteTypeCSchurSix.orbital 2 2 [x₁ ^ 2, x₂ ^ 2]) =
      16 * PowerSeries.coeff 8
        (normalizedOddNumerator (x₁ : ℚ) x₂ y₁ y₂) := by
  rw [coefficient_eight]
  simp [rankTwoPowerSumEval, FiniteTypeCSchurSix.orbital,
    FiniteTypeCSchurSix.partitions, QuarticOrbitalEleven.factorialRho,
    FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.powerSum, FiniteTypeCSchurSix.h1,
    FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.e1,
    FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.p1,
    FiniteTypeCSchurSix.p2]
  ring

theorem orbital_two_third_hc (x₁ x₂ : ℕ) (y₁ y₂ : ℚ) :
    oddVandermondeProduct (x₁ : ℚ) x₂ y₁ y₂ *
      rankTwoPowerSumEval (y₁ ^ 2) (y₂ ^ 2)
        (FiniteTypeCSchurSix.orbital 2 3 [x₁ ^ 2, x₂ ^ 2]) =
      64 * PowerSeries.coeff 10
        (normalizedOddNumerator (x₁ : ℚ) x₂ y₁ y₂) := by
  rw [coeff_normalizedOddNumerator]
  simp [rankTwoPowerSumEval, FiniteTypeCSchurSix.orbital,
    FiniteTypeCSchurSix.partitions, QuarticOrbitalEleven.factorialRho,
    FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.powerSum, FiniteTypeCSchurSix.h1,
    FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2,
    FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.p1,
    FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3,
    c, Finset.sum_range_succ]
  unfold oddVandermondeProduct
  ring

end
end QuaternionicSymmetry.OrbitalRankTwoHC
