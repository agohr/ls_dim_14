import QuaternionicSymmetry.GaussianCombination
import Mathlib.Probability.Independence.Integration

/-!
# The quadratic Wick identity in a commutative normed real algebra

The probability space here is the actual finite product of standard Gaussian
measures.  Thus the theorem below has no independence or distribution
hypotheses: both are supplied by the product construction.
-/

namespace QuaternionicSymmetry.GaussianAlgebra

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

variable {ι S : Type*} [Fintype ι] [DecidableEq ι]
  [NormedCommRing S] [NormedAlgebra ℝ S] [CompleteSpace S]

/-- The finite product probability measure of independent standard real Gaussians. -/
def standardMeasure : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι ↦ gaussianReal 0 1

/-- The algebra-valued linear Gaussian combination. -/
def combination (θ : ι → S) : (ι → ℝ) → S :=
  fun ω ↦ ∑ i, ω i • θ i

omit [DecidableEq ι] in
private theorem coordinate_hasLaw (i : ι) :
    HasLaw (fun ω : ι → ℝ ↦ ω i) (gaussianReal 0 1) standardMeasure :=
  (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).hasLaw

omit [DecidableEq ι] in
private theorem coordinate_independent :
    iIndepFun (fun i (ω : ι → ℝ) ↦ ω i) standardMeasure := by
  simpa [standardMeasure] using
    (iIndepFun_pi (μ := fun _ : ι ↦ gaussianReal 0 1) (X := fun _ x ↦ x)
      (fun _ ↦ aemeasurable_id))

omit [DecidableEq ι] in
private theorem coordinate_integrable_pow (i : ι) (n : ℕ) :
    Integrable (fun ω : ι → ℝ ↦ ω i ^ n) standardMeasure := by
  have h : Integrable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 1) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) n
  rw [← (coordinate_hasLaw i).map_eq] at h
  exact h.comp_aemeasurable (coordinate_hasLaw i).aemeasurable

omit [DecidableEq ι] in
private theorem coordinate_integral_one (i : ι) :
    (∫ ω : ι → ℝ, ω i ∂standardMeasure) = 0 := by
  simpa [pow_one] using
    (GaussianCombination.integral_pow_of_hasLaw (coordinate_hasLaw i) 1).trans
      (GaussianMoments.integral_odd_1 (1 : ℝ≥0))

omit [DecidableEq ι] in
private theorem coordinate_integral_square (i : ι) :
    (∫ ω : ι → ℝ, ω i ^ 2 ∂standardMeasure) = 1 := by
  rw [GaussianCombination.integral_pow_of_hasLaw (coordinate_hasLaw i) 2]
  simpa using GaussianMoments.integral_square (1 : ℝ≥0)

theorem coordinate_integral_mul (i j : ι) :
    (∫ ω : ι → ℝ, ω i * ω j ∂standardMeasure) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simpa [pow_two] using coordinate_integral_square i
  · rw [if_neg h]
    exact (coordinate_independent.indepFun h).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable |>.trans (by rw [coordinate_integral_one,
        coordinate_integral_one, mul_zero])

theorem coordinate_mul_integrable (i j : ι) :
    Integrable (fun ω : ι → ℝ ↦ ω i * ω j) standardMeasure := by
  by_cases h : i = j
  · subst j
    simpa [pow_two] using coordinate_integrable_pow i 2
  · exact (coordinate_independent.indepFun h).integrable_mul
      (by simpa [pow_one] using coordinate_integrable_pow i 1)
      (by simpa [pow_one] using coordinate_integrable_pow j 1)

/-- The quadratic Wick identity for a finite algebra-valued Gaussian combination. -/
theorem integral_combination_square (θ : ι → S) :
    (∫ ω : ι → ℝ, combination θ ω ^ 2 ∂standardMeasure) = ∑ i, θ i ^ 2 := by
  rw [show (fun ω : ι → ℝ ↦ combination θ ω ^ 2) =
      fun ω ↦ ∑ i, ∑ j, (ω i * ω j) • (θ i * θ j) by
    ext ω
    simp only [combination, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_smul, mul_comm (ω j) (ω i), mul_comm (θ j) (θ i)]]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · calc
        _ = ∑ j, (∫ ω : ι → ℝ, ω i * ω j ∂standardMeasure) • (θ i * θ j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact integral_smul_const _ _
        _ = θ i ^ 2 := by
          simp_rw [coordinate_integral_mul]
          simp [pow_two]
    · intro j _
      exact (coordinate_mul_integrable i j).smul_const _
  · intro i _
    exact integrable_finset_sum _ fun j _ ↦ (coordinate_mul_integrable i j).smul_const _

end
end QuaternionicSymmetry.GaussianAlgebra
