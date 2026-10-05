import QuaternionicSymmetry.GaussianAffineMoments
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Coefficients of the affine Gaussian moment polynomial. -/

namespace QuaternionicSymmetry.GaussianAffineCoefficients

open scoped BigOperators
open GaussianPolynomialExpectation GaussianAffineMoments

noncomputable section

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra ℝ S]

/-- The coefficient of degree `r` in an affine Gaussian moment selects the
unique binomial summand with `j = n-r`. -/
theorem coeff_expectation_affine (z : S) (θ : ι → S) (n r : ℕ) (hr : r ≤ n) :
    (GaussianPolynomialExpectation.expectation
      ((MvPolynomial.C (Polynomial.X * Polynomial.C z) +
        linearPolynomial (fun i => Polynomial.C (θ i))) ^ n)).coeff r =
      (Nat.choose n r : S) * z ^ r *
        GaussianMomentPolynomials.moment (n - r) (∑ i, θ i ^ 2) := by
  classical
  have hexpect := GaussianAffineMoments.expectation_affine
    (ι := ι) (S := Polynomial S) (Polynomial.X * Polynomial.C z)
    (fun i => Polynomial.C (θ i)) n
  rw [hexpect]
  let coeffHom : Polynomial S →+ S :=
    { toFun := fun p => p.coeff r
      map_zero' := by simp
      map_add' := by intro p q; exact Polynomial.coeff_add p q r }
  have hsum :
      (∑ j ∈ Finset.range (n + 1),
          (Nat.choose n j : Polynomial S) *
            (Polynomial.X * Polynomial.C z) ^ (n - j) *
            GaussianMomentPolynomials.moment j
              (∑ i, (Polynomial.C (θ i) : Polynomial S) ^ 2)).coeff r =
        ∑ j ∈ Finset.range (n + 1),
          ((Nat.choose n j : Polynomial S) *
            (Polynomial.X * Polynomial.C z) ^ (n - j) *
            GaussianMomentPolynomials.moment j
              (∑ i, (Polynomial.C (θ i) : Polynomial S) ^ 2)).coeff r := by
    change coeffHom (∑ j ∈ Finset.range (n + 1),
      (Nat.choose n j : Polynomial S) *
        (Polynomial.X * Polynomial.C z) ^ (n - j) *
        GaussianMomentPolynomials.moment j
          (∑ i, (Polynomial.C (θ i) : Polynomial S) ^ 2)) =
      ∑ j ∈ Finset.range (n + 1), coeffHom
        ((Nat.choose n j : Polynomial S) *
          (Polynomial.X * Polynomial.C z) ^ (n - j) *
          GaussianMomentPolynomials.moment j
            (∑ i, (Polynomial.C (θ i) : Polynomial S) ^ 2))
    rw [map_sum]
  rw [hsum]
  have hpow (k : ℕ) :
      (Polynomial.X * Polynomial.C z) ^ k =
        Polynomial.C (z ^ k) * Polynomial.X ^ k := by
    rw [Polynomial.X_mul_C, mul_pow, ← Polynomial.C_pow]
  have hmoment :
      (∑ i, (Polynomial.C (θ i) : Polynomial S) ^ 2) =
        Polynomial.C (∑ i, θ i ^ 2) := by
    rw [map_sum]
    simp only [Polynomial.C_pow]
  have hterm (j : ℕ) :
      ((Nat.choose n j : Polynomial S) *
        (Polynomial.X * Polynomial.C z) ^ (n - j) *
        GaussianMomentPolynomials.moment j
          (∑ i, (Polynomial.C (θ i) : Polynomial S) ^ 2)).coeff r =
        if r = n - j then
          (Nat.choose n j : S) * z ^ (n - j) *
            GaussianMomentPolynomials.moment j (∑ i, θ i ^ 2)
        else 0 := by
    rw [hpow, hmoment]
    have hCcast : (Nat.choose n j : Polynomial S) =
        Polynomial.C (Nat.choose n j : S) := by
      calc
        (Nat.choose n j : Polynomial S) =
            (Nat.choose n j) • (1 : Polynomial S) := by
              rw [nsmul_eq_mul]
              simp
        _ = (Nat.choose n j : S) • (1 : Polynomial S) := by
              rw [Nat.cast_smul_eq_nsmul]
        _ = Polynomial.C (Nat.choose n j : S) := by
              symm
              simpa using (Polynomial.C_mul' (Nat.choose n j : S)
                (1 : Polynomial S))
    have hmoment_map :
        GaussianMomentPolynomials.moment j (Polynomial.C (∑ i, θ i ^ 2)) =
          Polynomial.C (GaussianMomentPolynomials.moment j (∑ i, θ i ^ 2)) := by
      symm
      exact GaussianPolynomialExpectation.map_moment
        (Polynomial.C : S →+* Polynomial S) j (∑ i, θ i ^ 2)
    rw [hCcast, hmoment_map]
    calc
      (Polynomial.C (Nat.choose n j : S) *
          (Polynomial.C (z ^ (n - j)) * Polynomial.X ^ (n - j)) *
          Polynomial.C (GaussianMomentPolynomials.moment j (∑ i, θ i ^ 2))).coeff r =
          (Polynomial.C (Nat.choose n j : S) *
            Polynomial.C (z ^ (n - j)) *
            Polynomial.C (GaussianMomentPolynomials.moment j (∑ i, θ i ^ 2)) *
            Polynomial.X ^ (n - j)).coeff r := by ac_rfl
      _ = (Polynomial.C ((Nat.choose n j : S) * z ^ (n - j) *
            GaussianMomentPolynomials.moment j (∑ i, θ i ^ 2)) *
            Polynomial.X ^ (n - j)).coeff r := by
              rw [← Polynomial.C_mul, ← Polynomial.C_mul]
      _ = if r = n - j then
          (Nat.choose n j : S) * z ^ (n - j) *
            GaussianMomentPolynomials.moment j (∑ i, θ i ^ 2) else 0 := by
              rw [Polynomial.coeff_C_mul_X_pow]
  simp_rw [hterm]
  rw [Finset.sum_eq_single (n - r)]
  · have hsub : n - (n - r) = r := Nat.sub_sub_self hr
    rw [if_pos hsub.symm, hsub, Nat.choose_symm hr]
  · intro j hj hjne
    rw [if_neg]
    intro heq
    apply hjne
    have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hEq' : n = r + j := (Nat.sub_eq_iff_eq_add hjle).mp heq.symm
    omega
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.lt_succ_self _)))).elim

end
end QuaternionicSymmetry.GaussianAffineCoefficients
