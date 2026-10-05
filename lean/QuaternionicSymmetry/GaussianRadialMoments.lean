import QuaternionicSymmetry.GaussianPolynomialIntegration
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Radial moments of a finite standard Gaussian vector. -/

namespace QuaternionicSymmetry.GaussianRadialMoments

open scoped BigOperators
open GaussianPolynomialExpectation MvPolynomial

noncomputable section

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra ℝ S]

private theorem moment_add_two (n : ℕ) :
    GaussianMomentPolynomials.moment (n + 2) (1 : ℝ) =
      (n + 1 : ℝ) * GaussianMomentPolynomials.moment n (1 : ℝ) := by
  simpa only [GaussianMoments.integral_eq_moment, NNReal.coe_one, mul_one,
    Nat.cast_add, Nat.cast_one] using GaussianMoments.integral_pow_recurrence 1 n

theorem monomialMoment_add_two (d : ι →₀ ℕ) (i : ι) :
    monomialMoment (d + Finsupp.single i 2) = (d i + 1 : ℝ) * monomialMoment d := by
  unfold monomialMoment
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => GaussianMomentPolynomials.moment (d j) 1)
      (Finset.mem_univ i)]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, moment_add_two]
  rw [mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [Finsupp.single_eq_of_ne hji]

/-- The polynomial form of Gaussian integration by parts, with no analytic
assumptions on the coefficient algebra. -/
theorem expectation_sq_mul (i : ι) (p : MvPolynomial ι S) :
    expectation (X i ^ 2 * p) = expectation p + expectation (X i * pderiv i p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [X_mul_pderiv_monomial, map_nsmul]
      rw [X_pow_eq_monomial, monomial_mul, one_mul, add_comm, expectation_monomial,
        monomialMoment_add_two, expectation_monomial]
      simp only [map_mul, map_add, map_natCast, map_one, nsmul_eq_mul]
      ring
  | add p q hp hq =>
      simp only [mul_add, map_add, hp, hq]
      ring

def radial : MvPolynomial ι S := ∑ i, X i ^ 2

omit [Algebra ℝ S] in
theorem pderiv_radial (i : ι) : pderiv i (radial : MvPolynomial ι S) = 2 * X i := by
  simp [radial, map_sum, Pi.single_apply, Finset.sum_ite_eq']

omit [Algebra ℝ S] in
theorem radial_euler (m : ℕ) :
    ∑ i, X i * pderiv i ((radial : MvPolynomial ι S) ^ m) =
      (2 * m) • (radial : MvPolynomial ι S) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        _ = (∑ i, X i * pderiv i ((radial : MvPolynomial ι S) ^ m)) * radial +
            (2 * radial ^ m) * ∑ i : ι, X i ^ 2 := by
          simp only [pow_succ, pderiv_mul, pderiv_radial, Finset.sum_mul, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (2 * (m + 1)) • (radial : MvPolynomial ι S) ^ (m + 1) := by
          rw [ih]
          change _ + (2 * radial ^ m) * radial = _
          simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
            Nat.cast_one, pow_succ]
          ring

theorem expectation_radial_succ (m : ℕ) :
    expectation ((radial : MvPolynomial ι S) ^ (m + 1)) =
      (Fintype.card ι + 2 * m) • expectation ((radial : MvPolynomial ι S) ^ m) := by
  calc
    _ = ∑ i, expectation (X i ^ 2 * (radial : MvPolynomial ι S) ^ m) := by
      rw [pow_succ', radial, Finset.sum_mul, map_sum]
    _ = ∑ i, (expectation ((radial : MvPolynomial ι S) ^ m) +
        expectation (X i * pderiv i (radial ^ m))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact expectation_sq_mul i _
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
        radial_euler, map_nsmul, add_nsmul]

omit [DecidableEq ι] in
@[simp] theorem expectation_one : expectation (1 : MvPolynomial ι S) = 1 := by
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, expectation_monomial]
  simp [monomialMoment]

/-- The radial moments in real dimension three are the odd double factorials. -/
theorem expectation_radial_three (m : ℕ) :
    expectation ((radial : MvPolynomial (Fin 3) S) ^ m) =
      (Nat.doubleFactorial (2 * m + 1) : S) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [expectation_radial_succ, ih, nsmul_eq_mul, Nat.doubleFactorial_add_one (2 * (m + 1))]
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
      simp only [Fintype.card_fin, Nat.cast_mul]
      congr 1
      congr 1
      omega

omit [DecidableEq ι] [Algebra ℝ S] in
@[simp] theorem eval_radial (x : ι → S) :
    MvPolynomial.eval x (radial : MvPolynomial ι S) = ∑ i, x i ^ 2 := by
  simp [radial]

open MeasureTheory

omit [DecidableEq ι] in
theorem radial_pow_integrable (m : ℕ) :
    Integrable (fun x : ι → ℝ => (∑ i, x i ^ 2) ^ m)
      GaussianPolynomialIntegration.standardMeasure := by
  simpa using GaussianPolynomialIntegration.polynomial_integrable
    ((radial : MvPolynomial ι ℝ) ^ m)

/-- The computed radial moments are the actual integrals on the product law. -/
theorem integral_radial_three (m : ℕ) :
    (∫ x : Fin 3 → ℝ, (∑ i, x i ^ 2) ^ m
      ∂GaussianPolynomialIntegration.standardMeasure) =
        (Nat.doubleFactorial (2 * m + 1) : ℝ) := by
  simpa only [map_pow, eval_radial, expectation_radial_three] using
    GaussianPolynomialIntegration.integral_polynomial ((radial : MvPolynomial (Fin 3) ℝ) ^ m)

end
end QuaternionicSymmetry.GaussianRadialMoments
