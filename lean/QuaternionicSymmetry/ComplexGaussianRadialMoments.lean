import QuaternionicSymmetry.ComplexGaussianPolynomial
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Factorial.Basic

/-! Integration by parts and radial moments for factorial (complex-radial) weights. -/

namespace QuaternionicSymmetry.ComplexGaussianRadialMoments

open scoped BigOperators
open ComplexGaussianPolynomial MvPolynomial
open MeasureTheory

noncomputable section

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra ℝ S]

theorem monomialMoment_add_one (d : ι →₀ ℕ) (i : ι) :
    monomialMoment (d + Finsupp.single i 1) =
      (d i + 1 : ℝ) * monomialMoment d := by
  unfold monomialMoment
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => ((d j).factorial : ℝ))
      (Finset.mem_univ i)]
  have hprod :
      Finset.prod (Finset.univ.erase i)
          (fun x => (((d + (Finsupp.single i 1 : ι →₀ ℕ)) x).factorial : ℝ)) =
        Finset.prod (Finset.univ.erase i) (fun x => ((d x).factorial : ℝ)) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
    simp [Finsupp.add_apply, Finsupp.single_eq_of_ne hxi]
  simp only [Finsupp.add_apply] at hprod ⊢
  rw [hprod]
  simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  ring

theorem expectation_mul (i : ι) (p : MvPolynomial ι S) :
    expectation (X i * p) = expectation p + expectation (X i * pderiv i p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      conv_lhs =>
        rw [← pow_one (X i), ← monomial_single_add]
      rw [show X i * pderiv i (monomial d c) = d i • monomial d c by
        exact X_mul_pderiv_monomial]
      rw [map_nsmul]
      rw [add_comm,
        expectation_monomial, monomialMoment_add_one, expectation_monomial]
      simp only [map_mul, map_add, map_natCast, map_one, nsmul_eq_mul]
      ring
  | add p q hp hq =>
      simp only [mul_add, map_add, hp, hq]
      ring

def linearRadial : MvPolynomial ι S := ∑ i, X i

omit [DecidableEq ι] [Algebra ℝ S] in
@[simp] theorem eval_linearRadial (x : ι → S) :
    MvPolynomial.eval x (linearRadial : MvPolynomial ι S) = ∑ i, x i := by
  simp [linearRadial]

omit [Algebra ℝ S] in
theorem pderiv_linearRadial (i : ι) :
    pderiv i (linearRadial : MvPolynomial ι S) = 1 := by
  simp [linearRadial, map_sum, Pi.single_apply, Finset.sum_ite_eq']

omit [Algebra ℝ S] in
theorem linearRadial_euler (m : ℕ) :
    ∑ i, X i * pderiv i ((linearRadial : MvPolynomial ι S) ^ m) =
      m • (linearRadial : MvPolynomial ι S) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        _ = (∑ i, X i * pderiv i ((linearRadial : MvPolynomial ι S) ^ m)) * linearRadial +
            linearRadial ^ m * ∑ i : ι, X i := by
          simp only [pow_succ, pderiv_mul, pderiv_linearRadial, Finset.sum_mul,
            Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (m + 1) • (linearRadial : MvPolynomial ι S) ^ (m + 1) := by
          rw [ih]
          change _ + linearRadial ^ m * linearRadial = _
          simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, pow_succ]
          ring

theorem expectation_linearRadial_succ (m : ℕ) :
    expectation ((linearRadial : MvPolynomial ι S) ^ (m + 1)) =
      (Fintype.card ι + m) • expectation ((linearRadial : MvPolynomial ι S) ^ m) := by
  calc
    _ = ∑ i, expectation (X i * (linearRadial : MvPolynomial ι S) ^ m) := by
      rw [pow_succ', linearRadial, Finset.sum_mul, map_sum]
    _ = ∑ i, (expectation ((linearRadial : MvPolynomial ι S) ^ m) +
        expectation (X i * pderiv i (linearRadial ^ m))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact expectation_mul i _
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
        linearRadial_euler, map_nsmul, add_nsmul]

omit [DecidableEq ι] in
@[simp] theorem expectation_one :
    expectation (1 : MvPolynomial ι S) = 1 := by
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, expectation_monomial]
  simp [monomialMoment]

theorem expectation_linearRadial (m : ℕ) :
    expectation ((linearRadial : MvPolynomial ι S) ^ m) =
      (Fintype.card ι).ascFactorial m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [expectation_linearRadial_succ, ih, nsmul_eq_mul,
        Nat.ascFactorial_succ]
      simp only [Nat.cast_add, Nat.cast_mul]

omit [DecidableEq ι] in
theorem linearRadial_pow_integrable (m : ℕ) :
    Integrable (fun ω : ι → Fin 2 → ℝ =>
      (∑ i, ‖ComplexGaussianProduct.vector ω i‖ ^ 2) ^ m)
      ComplexGaussianProduct.standardProductMeasure := by
  simpa only [map_pow, eval_linearRadial] using
    ComplexGaussianPolynomial.polynomial_integrable
      ((linearRadial : MvPolynomial ι ℝ) ^ m)

omit [DecidableEq ι] in
theorem integral_linearRadial (m : ℕ) :
    (∫ ω : ι → Fin 2 → ℝ,
      (∑ i, ‖ComplexGaussianProduct.vector ω i‖ ^ 2) ^ m
      ∂ComplexGaussianProduct.standardProductMeasure) =
      ((Fintype.card ι).ascFactorial m : ℝ) := by
  letI : DecidableEq ι := Classical.decEq ι
  simpa only [map_pow, eval_linearRadial, expectation_linearRadial] using
    ComplexGaussianPolynomial.integral_polynomial
      ((linearRadial : MvPolynomial ι ℝ) ^ m)

end
end QuaternionicSymmetry.ComplexGaussianRadialMoments
