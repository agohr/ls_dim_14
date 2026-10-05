import QuaternionicSymmetry.GaussianMomentPolynomials
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Coefficientwise Gaussian expectation, as a linear map over any real algebra.

The comparison with actual scalar integration is made separately. This algebraic
construction also works in rings with nilpotents, including even exterior forms.
-/

namespace QuaternionicSymmetry.GaussianPolynomialExpectation

open scoped BigOperators

noncomputable section

variable {ι S T : Type*} [Fintype ι] [CommRing S] [Algebra ℝ S]
    [CommRing T] [Algebra ℝ T]

def monomialMoment (d : ι →₀ ℕ) : ℝ :=
  ∏ i, GaussianMomentPolynomials.moment (d i) 1

def expectation : MvPolynomial ι S →ₗ[S] S :=
  Finsupp.linearCombination S (fun d => algebraMap ℝ S (monomialMoment d))

@[simp] theorem expectation_monomial (d : ι →₀ ℕ) (a : S) :
    expectation (MvPolynomial.monomial d a) = a * algebraMap ℝ S (monomialMoment d) := by
  exact Finsupp.linearCombination_single _ _ _

/-- Evaluation of the coefficients commutes with Gaussian expectation. -/
theorem expectation_map (f : S →ₐ[ℝ] T) (p : MvPolynomial ι S) :
    f (expectation p) = expectation (MvPolynomial.map f.toRingHom p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a => simp
  | add p q hp hq => simp [hp, hq]

def linearPolynomial (θ : ι → S) : MvPolynomial ι S :=
  ∑ i, MvPolynomial.C (θ i) * MvPolynomial.X i

@[simp] theorem map_linearPolynomial (f : S →ₐ[ℝ] T) (θ : ι → S) :
    MvPolynomial.map f.toRingHom (linearPolynomial θ) = linearPolynomial (fun i => f (θ i)) := by
  simp [linearPolynomial]

theorem eval_linearPolynomial (θ : ι → S) (ω : ι → ℝ) :
    MvPolynomial.eval (fun i => algebraMap ℝ S (ω i)) (linearPolynomial θ) =
      ∑ i, ω i • θ i := by
  simp only [linearPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

omit [Algebra ℝ S] [Algebra ℝ T] in
theorem map_moment (f : S →+* T) (n : ℕ) (v : S) :
    f (GaussianMomentPolynomials.moment n v) = GaussianMomentPolynomials.moment n (f v) := by
  unfold GaussianMomentPolynomials.moment
  split_ifs <;> simp

theorem algHom_moment (f : S →ₐ[ℝ] T) (n : ℕ) (v : S) :
    f (GaussianMomentPolynomials.moment n v) = GaussianMomentPolynomials.moment n (f v) := by
  unfold GaussianMomentPolynomials.moment
  split_ifs <;> simp

end
end QuaternionicSymmetry.GaussianPolynomialExpectation
