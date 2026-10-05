import QuaternionicSymmetry.GaussianUniversalWick
import QuaternionicSymmetry.GaussianPolynomialExpectation
import Mathlib.Tactic

/-! Exact binomial moments for an affine polynomial observable. -/

namespace QuaternionicSymmetry.GaussianAffineMoments

open scoped BigOperators
open GaussianPolynomialExpectation GaussianUniversalWick

noncomputable section

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra ℝ S]

omit [DecidableEq ι] in
/-- Coefficientwise expectation factors a constant polynomial. -/
theorem expectation_C_mul (c : S) (p : MvPolynomial ι S) :
    expectation (MvPolynomial.C c * p) = c * expectation p := by
  rw [MvPolynomial.C_mul', map_smul]
  rfl

/-- The exact formal Gaussian moment of an affine linear polynomial. -/
theorem expectation_affine (z : S) (θ : ι → S) (n : ℕ) :
    expectation ((MvPolynomial.C z + linearPolynomial θ) ^ n) =
      ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : S) * z ^ (n - j) *
          GaussianMomentPolynomials.moment j (∑ i, θ i ^ 2) := by
  rw [add_comm (MvPolynomial.C z) (linearPolynomial θ), add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hcast : (Nat.choose n j : MvPolynomial ι S) =
      (Nat.choose n j) • (1 : MvPolynomial ι S) := by
    rw [nsmul_eq_mul]
    simp
  rw [hcast]
  simp only [mul_one, nsmul_eq_mul]
  have hCcast : (Nat.choose n j : MvPolynomial ι S) =
      MvPolynomial.C (Nat.choose n j : S) := by
    calc
      MvPolynomial.C (Nat.choose n j : S) =
          (Nat.choose n j : S) • (1 : MvPolynomial ι S) := by
            simpa using (MvPolynomial.C_mul' (a := (Nat.choose n j : S))
              (p := (1 : MvPolynomial ι S)))
      _ = (Nat.choose n j) • (1 : MvPolynomial ι S) := by
        rw [Nat.cast_smul_eq_nsmul]
      _ = (Nat.choose n j : MvPolynomial ι S) := hcast.symm
  rw [hCcast]
  have hpoly :
      linearPolynomial θ ^ j * MvPolynomial.C z ^ (n - j) *
          MvPolynomial.C (Nat.choose n j : S) =
        MvPolynomial.C ((Nat.choose n j : S) * z ^ (n - j)) *
          linearPolynomial θ ^ j := by
    rw [← MvPolynomial.C_pow]
    calc
      linearPolynomial θ ^ j * MvPolynomial.C (z ^ (n - j)) *
            MvPolynomial.C (Nat.choose n j : S) =
          (MvPolynomial.C (z ^ (n - j)) *
            MvPolynomial.C (Nat.choose n j : S)) * linearPolynomial θ ^ j := by
              ac_rfl
      _ = MvPolynomial.C (z ^ (n - j) * (Nat.choose n j : S)) *
            linearPolynomial θ ^ j := by rw [← MvPolynomial.C_mul]
      _ = MvPolynomial.C ((Nat.choose n j : S) * z ^ (n - j)) *
            linearPolynomial θ ^ j := by
              congr 1
              ring_nf
  rw [hpoly, expectation_C_mul, GaussianUniversalWick.moment]

end
end QuaternionicSymmetry.GaussianAffineMoments
