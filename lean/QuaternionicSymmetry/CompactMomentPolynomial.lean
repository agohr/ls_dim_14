import QuaternionicSymmetry.CompactPolynomialAverage
import QuaternionicSymmetry.GaussianPolynomialExpectation
import Mathlib.Algebra.MvPolynomial.Funext

/-!
Universal moment polynomials and continuation from real numerical identities
to every real commutative algebra. Continuation is coefficientwise, so it
applies to nilpotent even-form coefficients without diagonalizing them.
-/

namespace QuaternionicSymmetry.CompactMomentPolynomial

open MeasureTheory GaussianPolynomialExpectation CompactPolynomialAverage
open scoped MeasureTheory

noncomputable section

variable {Ω β S : Type*} [MeasurableSpace Ω] [Fintype β]
  [CommRing S] [Algebra ℝ S]

/-- The universal polynomial whose scalar specializations are actual moments. -/
def moment (μ : Measure Ω) (f : Ω → β → ℝ) (k : ℕ) : MvPolynomial β ℝ :=
  average μ f ((linearPolynomial (fun b : β => MvPolynomial.X b)) ^ k)

/-- Substitution of arbitrary algebra coefficients commutes with the moment. -/
theorem aeval_moment (μ : Measure Ω) (f : Ω → β → ℝ) (k : ℕ) (η : β → S) :
    MvPolynomial.aeval η (moment μ f k) = average μ f ((linearPolynomial η) ^ k) := by
  unfold moment
  rw [average_map]
  simp only [map_pow, map_linearPolynomial, MvPolynomial.aeval_X]

variable [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → β → ℝ) (hf : Continuous f)

include hf

/-- Numerical evaluation of the universal moment equals its Haar/measure integral. -/
theorem eval_moment (k : ℕ) (x : β → ℝ) :
    MvPolynomial.eval x (moment μ f k) = ∫ ω, (∑ b, f ω b * x b) ^ k ∂μ := by
  rw [← MvPolynomial.aeval_eq_eval, aeval_moment]
  have h := integral_evaluation μ f hf (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
    ((linearPolynomial x) ^ k)
  simpa only [LinearMap.id_apply, map_pow, eval_linearPolynomial, smul_eq_mul] using h.symm

/-- A numerical polynomial identity for all real coefficients determines
the universal moment polynomial. -/
theorem moment_eq_of_integral_eq (k : ℕ) (p : MvPolynomial β ℝ)
    (hp : ∀ x : β → ℝ, (∫ ω, (∑ b, f ω b * x b) ^ k ∂μ) = p.eval x) :
    moment μ f k = p := by
  apply MvPolynomial.funext
  intro x
  rw [eval_moment μ f hf]
  exact hp x

/-- Universal polynomial continuation, including into nonreduced algebras. -/
theorem average_eq_aeval_of_integral_eq (k : ℕ) (p : MvPolynomial β ℝ)
    (hp : ∀ x : β → ℝ, (∫ ω, (∑ b, f ω b * x b) ^ k ∂μ) = p.eval x)
    (η : β → S) :
    average μ f ((linearPolynomial η) ^ k) = MvPolynomial.aeval η p := by
  rw [← aeval_moment, moment_eq_of_integral_eq μ f hf k p hp]

/-- It suffices to establish a numerical moment identity on a product of
infinite sets. This permits a regular spectral test region and does not require
division or distinct eigenvalues after specialization to a coefficient algebra. -/
theorem moment_eq_of_integral_eq_on (k : ℕ) (p : MvPolynomial β ℝ)
    (s : β → Set ℝ) (hs : ∀ b, (s b).Infinite)
    (hp : ∀ x ∈ Set.pi Set.univ s,
      (∫ ω, (∑ b, f ω b * x b) ^ k ∂μ) = p.eval x) :
    moment μ f k = p := by
  apply MvPolynomial.funext_set s hs
  intro x hx
  rw [eval_moment μ f hf]
  exact hp x hx

theorem average_eq_aeval_of_integral_eq_on (k : ℕ) (p : MvPolynomial β ℝ)
    (s : β → Set ℝ) (hs : ∀ b, (s b).Infinite)
    (hp : ∀ x ∈ Set.pi Set.univ s,
      (∫ ω, (∑ b, f ω b * x b) ^ k ∂μ) = p.eval x)
    (η : β → S) :
    average μ f ((linearPolynomial η) ^ k) = MvPolynomial.aeval η p := by
  rw [← aeval_moment, moment_eq_of_integral_eq_on μ f hf k p s hs hp]

end
end QuaternionicSymmetry.CompactMomentPolynomial
