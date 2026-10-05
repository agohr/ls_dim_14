import QuaternionicSymmetry.FiniteTypeCSchurSix
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Rank-one normalization of the symplectic Harish--Chandra kernel

For `USp(2)`, the odd determinant in Forrester--Ipsen--Liu--Zhang,
arXiv:1711.10691v1, Eq. (1.8), has one entry.  Its normalizing constant is
`1!/2`, so the source expression is `sinh(x*y)/(x*y)`.  We prove its
coefficient identity as an equality of formal power series, with no
integrability or analytic continuation assumption.  The source uses half the
complex trace.  Doubling the trace rescales its `2k`-th coefficient by `4^k`.

No claim about the all-rank Haar integral is made here. -/

namespace QuaternionicSymmetry.OrbitalRankOneHC

open PowerSeries

noncomputable section

/-- The rank-one odd-determinant quotient as a formal rational series. -/
def oddKernel : PowerSeries ℚ :=
  PowerSeries.mk fun m => (1 - (-1 : ℚ) ^ (m + 1)) / (2 * (Nat.factorial (m + 1) : ℚ))

/-- This equality makes the `sinh(x)/x` meaning of `oddKernel` precise
without taking a quotient by the nonunit formal variable `X`. -/
theorem X_mul_oddKernel :
    (PowerSeries.X : PowerSeries ℚ) * oddKernel =
      PowerSeries.C (1 / 2 : ℚ) *
        (PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) := by
  ext m
  cases m with
  | zero =>
      have h : PowerSeries.constantCoeff
          (PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) = (1 : ℚ) := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simp
      simp [h]
  | succ m =>
      simp [oddKernel,
        PowerSeries.coeff_exp, PowerSeries.coeff_rescale]
      ring

/-- The coefficient in the source's half-complex-trace convention. -/
theorem coeff_oddKernel_even (k : ℕ) :
    PowerSeries.coeff (2 * k) oddKernel = 1 / (Nat.factorial (2 * k + 1) : ℚ) := by
  simp [oddKernel, pow_add, pow_mul]
  ring

/-- Odd coefficients vanish: the normalized rank-one kernel is even. -/
theorem coeff_oddKernel_odd (k : ℕ) :
    PowerSeries.coeff (2 * k + 1) oddKernel = 0 := by
  simp [oddKernel, pow_add, pow_mul]

/-- Replacing the half trace by the full trace supplies exactly `4^k`. -/
theorem coeff_fullTrace_even (k : ℕ) :
    PowerSeries.coeff (2 * k) (PowerSeries.rescale 2 oddKernel) =
      (4 : ℚ) ^ k / (Nat.factorial (2 * k + 1) : ℚ) := by
  rw [PowerSeries.coeff_rescale, coeff_oddKernel_even]
  rw [show (2 : ℚ) ^ (2 * k) = (4 : ℚ) ^ k by rw [pow_mul]; norm_num]
  ring

theorem coeff_fullTrace_odd (k : ℕ) :
    PowerSeries.coeff (2 * k + 1) (PowerSeries.rescale 2 oddKernel) = 0 := by
  simp [coeff_oddKernel_odd]

/-- The first coefficient of the finite type-C Schur orbital at rank one
agrees with the doubled-trace odd-determinant coefficient. -/
theorem orbital_one_first (a : ℕ) :
    FiniteTypeCSchurSix.orbital 1 1 [a] =
      MvPolynomial.C ((4 : ℚ) * (a : ℚ) / 6) *
        FiniteTypeCSchurSix.p1 := by
  simp [FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions,
    QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.schurValue,
    FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum,
    FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.p1]
  rw [show (a : FiniteTypeCSchurSix.P) = MvPolynomial.C (a : ℚ) by simp]
  simp only [← MvPolynomial.C_mul]
  congr 1
  ring

theorem orbital_one_second (a : ℕ) :
    FiniteTypeCSchurSix.orbital 1 2 [a] =
      MvPolynomial.C ((a : ℚ) ^ 2 / 15) *
        (FiniteTypeCSchurSix.p1 ^ 2 + FiniteTypeCSchurSix.p2) := by
  apply MvPolynomial.funext
  intro v
  simp [FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions,
    QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.schurValue,
    FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum,
    FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2,
    FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2]
  ring

/-- Substitution of the actual rank-one power sums `p_j = b^j`.  In the
universal polynomial algebra these `p_j` remain independent; the orbital
comparison is true on this spectral locus. -/
def rankOnePowerSumEval (b : ℚ) : FiniteTypeCSchurSix.P →ₐ[ℚ] ℚ :=
  MvPolynomial.aeval fun i => b ^ (i.val + 1)

theorem orbital_one_first_hc (a : ℕ) (b : ℚ) :
    rankOnePowerSumEval b (FiniteTypeCSchurSix.orbital 1 1 [a]) =
      (a * b : ℚ) * PowerSeries.coeff 2 (PowerSeries.rescale 2 oddKernel) := by
  rw [orbital_one_first, coeff_fullTrace_even 1]
  simp [rankOnePowerSumEval, FiniteTypeCSchurSix.p1]
  ring

theorem orbital_one_second_hc (a : ℕ) (b : ℚ) :
    rankOnePowerSumEval b (FiniteTypeCSchurSix.orbital 1 2 [a]) =
      (a * b : ℚ) ^ 2 * PowerSeries.coeff 4 (PowerSeries.rescale 2 oddKernel) := by
  rw [orbital_one_second, coeff_fullTrace_even 2]
  simp [rankOnePowerSumEval, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2]
  ring

theorem orbital_one_third_hc (a : ℕ) (b : ℚ) :
    rankOnePowerSumEval b (FiniteTypeCSchurSix.orbital 1 3 [a]) =
      (a * b : ℚ) ^ 3 * PowerSeries.coeff 6 (PowerSeries.rescale 2 oddKernel) := by
  rw [coeff_fullTrace_even 3]
  simp [rankOnePowerSumEval, FiniteTypeCSchurSix.orbital,
    FiniteTypeCSchurSix.partitions, QuarticOrbitalEleven.factorialRho,
    FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.powerSum,
    FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.e1,
    FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3]
  ring

theorem orbital_one_fourth_hc (a : ℕ) (b : ℚ) :
    rankOnePowerSumEval b (FiniteTypeCSchurSix.orbital 1 4 [a]) =
      (a * b : ℚ) ^ 4 * PowerSeries.coeff 8 (PowerSeries.rescale 2 oddKernel) := by
  rw [coeff_fullTrace_even 4]
  simp [rankOnePowerSumEval, FiniteTypeCSchurSix.orbital,
    FiniteTypeCSchurSix.partitions, QuarticOrbitalEleven.factorialRho,
    FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.powerSum, FiniteTypeCSchurSix.h1,
    FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3,
    FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.e1,
    FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.p1,
    FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3,
    FiniteTypeCSchurSix.p4]
  ring

theorem orbital_one_fifth_hc (a : ℕ) (b : ℚ) :
    rankOnePowerSumEval b (FiniteTypeCSchurSix.orbital 1 5 [a]) =
      (a * b : ℚ) ^ 5 * PowerSeries.coeff 10 (PowerSeries.rescale 2 oddKernel) := by
  rw [coeff_fullTrace_even 5]
  simp [rankOnePowerSumEval, FiniteTypeCSchurSix.orbital,
    FiniteTypeCSchurSix.partitions, QuarticOrbitalEleven.factorialRho,
    FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.powerSum, FiniteTypeCSchurSix.h1,
    FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3,
    FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2,
    FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4,
    FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.p1,
    FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3,
    FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5]
  ring

theorem orbital_one_sixth_hc (a : ℕ) (b : ℚ) :
    rankOnePowerSumEval b (FiniteTypeCSchurSix.orbital 1 6 [a]) =
      (a * b : ℚ) ^ 6 * PowerSeries.coeff 12 (PowerSeries.rescale 2 oddKernel) := by
  rw [coeff_fullTrace_even 6]
  simp [rankOnePowerSumEval, FiniteTypeCSchurSix.orbital,
    FiniteTypeCSchurSix.partitions, QuarticOrbitalEleven.factorialRho,
    FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.powerSum, FiniteTypeCSchurSix.h1,
    FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3,
    FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1,
    FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5,
    FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1,
    FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3,
    FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  ring

/-- The existing finite type-C Schur construction, on the actual rank-one
spectral locus, agrees in every represented weight with the coefficient of
the source's odd determinant after full-trace rescaling. -/
theorem orbital_one_hc (a : ℕ) (b : ℚ) (k : ℕ) (hk : k ≤ 6) :
    rankOnePowerSumEval b (FiniteTypeCSchurSix.orbital 1 k [a]) =
      (a * b : ℚ) ^ k *
        PowerSeries.coeff (2 * k) (PowerSeries.rescale 2 oddKernel) := by
  interval_cases k
  · simp [FiniteTypeCSchurSix.orbital_zero, oddKernel]
  · simpa using orbital_one_first_hc a b
  · simpa using orbital_one_second_hc a b
  · simpa using orbital_one_third_hc a b
  · simpa using orbital_one_fourth_hc a b
  · simpa using orbital_one_fifth_hc a b
  · simpa using orbital_one_sixth_hc a b

/-- A universal polynomial substitution for the rank-one power sums. -/
def rankOnePowerSumPolynomial :
    FiniteTypeCSchurSix.P →ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.aeval fun i => Polynomial.X ^ (i.val + 1)

private theorem eval_rankOnePowerSumPolynomial (b : ℚ)
    (P : FiniteTypeCSchurSix.P) :
    (rankOnePowerSumPolynomial P).eval b = rankOnePowerSumEval b P := by
  rw [← Polynomial.coe_aeval_eq_eval]
  simp [rankOnePowerSumPolynomial, rankOnePowerSumEval,
    MvPolynomial.comp_aeval_apply]

/-- The rank-one matching is a polynomial identity, so it survives
evaluation in any commutative rational algebra, including an even-form
algebra with nilpotent elements. -/
theorem orbital_one_polynomial (a k : ℕ) (hk : k ≤ 6) :
    rankOnePowerSumPolynomial (FiniteTypeCSchurSix.orbital 1 k [a]) =
      Polynomial.C ((a : ℚ) ^ k *
        PowerSeries.coeff (2 * k) (PowerSeries.rescale 2 oddKernel)) *
        Polynomial.X ^ k := by
  apply Polynomial.funext
  intro b
  rw [eval_rankOnePowerSumPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [orbital_one_hc a b k hk]
  ring

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem orbital_one_eval (a k : ℕ) (hk : k ≤ 6) (b : R) :
    MvPolynomial.aeval (fun i : Fin 6 => b ^ (i.val + 1))
        (FiniteTypeCSchurSix.orbital 1 k [a]) =
      algebraMap ℚ R ((a : ℚ) ^ k *
        PowerSeries.coeff (2 * k) (PowerSeries.rescale 2 oddKernel)) * b ^ k := by
  have h := congrArg (Polynomial.aeval b) (orbital_one_polynomial a k hk)
  simpa [rankOnePowerSumPolynomial, MvPolynomial.comp_aeval_apply] using h

end
end QuaternionicSymmetry.OrbitalRankOneHC
