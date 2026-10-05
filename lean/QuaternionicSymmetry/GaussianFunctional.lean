import QuaternionicSymmetry.GaussianAlgebraFourth
import QuaternionicSymmetry.GaussianPairings

/-! Gaussian moments tested against linear functionals.

Only the scalar output is integrated. The coefficient algebra needs no norm or
topology, so these statements apply directly to even exterior expressions.
-/

namespace QuaternionicSymmetry.GaussianFunctional

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra ℝ S]

abbrev standardMeasure : Measure (ι → ℝ) := GaussianAlgebra.standardMeasure

def combination (θ : ι → S) (ω : ι → ℝ) : S := ∑ i, ω i • θ i

omit [DecidableEq ι] in
private theorem square_expansion (L : S →ₗ[ℝ] ℝ) (θ : ι → S) (ω : ι → ℝ) :
    L (combination θ ω ^ 2) = ∑ i, ∑ j, (ω i * ω j) * L (θ i * θ j) := by
  simp only [combination, pow_two, Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_mul_smul, map_smul, smul_eq_mul]
  rw [mul_comm (ω j) (ω i), mul_comm (θ j) (θ i)]

theorem square_integrable (L : S →ₗ[ℝ] ℝ) (θ : ι → S) :
    Integrable (fun ω : ι → ℝ => L (combination θ ω ^ 2)) standardMeasure := by
  simp_rw [square_expansion]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (GaussianAlgebra.coordinate_mul_integrable i j).mul_const _

theorem integral_square (L : S →ₗ[ℝ] ℝ) (θ : ι → S) :
    (∫ ω : ι → ℝ, L (combination θ ω ^ 2) ∂standardMeasure) = L (∑ i, θ i ^ 2) := by
  simp_rw [square_expansion]
  rw [integral_finset_sum]
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · simp_rw [integral_mul_const, GaussianAlgebra.coordinate_integral_mul]
      simp [pow_two]
    · intro j _
      exact (GaussianAlgebra.coordinate_mul_integrable i j).mul_const _
  · intro i _
    exact integrable_finset_sum _ fun j _ =>
      (GaussianAlgebra.coordinate_mul_integrable i j).mul_const _

omit [DecidableEq ι] in
private theorem fourth_expansion (L : S →ₗ[ℝ] ℝ) (θ : ι → S) (ω : ι → ℝ) :
    L (combination θ ω ^ 4) = ∑ i, ∑ j, ∑ k, ∑ l,
      (ω i * ω j * ω k * ω l) * L (θ i * θ j * θ k * θ l) := by
  have h : combination θ ω ^ 4 = ∑ i, ∑ j, ∑ k, ∑ l,
      (ω i * ω j * ω k * ω l) • (θ i * θ j * θ k * θ l) := by
    simp only [combination, pow_succ, pow_zero, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    simp only [one_mul, Algebra.smul_def, map_mul]
    ring
  rw [h]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem fourth_integrable (L : S →ₗ[ℝ] ℝ) (θ : ι → S) :
    Integrable (fun ω : ι → ℝ => L (combination θ ω ^ 4)) standardMeasure := by
  simp_rw [fourth_expansion]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
      (GaussianAlgebraFourth.coordinate_mixed_fourth_integrable i j k l).mul_const _

theorem integral_fourth (L : S →ₗ[ℝ] ℝ) (θ : ι → S) :
    (∫ ω : ι → ℝ, L (combination θ ω ^ 4) ∂standardMeasure) =
      L (3 * (∑ i, θ i ^ 2) ^ 2) := by
  simp_rw [fourth_expansion]
  have hi (i j k l : ι) : Integrable (fun ω : ι → ℝ =>
      (ω i * ω j * ω k * ω l) * L (θ i * θ j * θ k * θ l)) standardMeasure :=
    (GaussianAlgebraFourth.coordinate_mixed_fourth_integrable i j k l).mul_const _
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        ∫ ω : ι → ℝ, (ω i * ω j * ω k * ω l) * L (θ i * θ j * θ k * θ l)
          ∂standardMeasure := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro j _
          rw [integral_finset_sum]
          · apply Finset.sum_congr rfl
            intro k _
            exact integral_finset_sum _ fun l _ => hi i j k l
          · intro k _
            exact integrable_finset_sum _ fun l _ => hi i j k l
        · intro j _
          exact integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => hi i j k l
      · intro i _
        exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
          integrable_finset_sum _ fun l _ => hi i j k l
    _ = L (∑ i, ∑ j, ∑ k, ∑ l,
        (GaussianPairings.delta i j * GaussianPairings.delta k l +
          GaussianPairings.delta i k * GaussianPairings.delta j l +
          GaussianPairings.delta i l * GaussianPairings.delta j k) *
          θ i * θ j * θ k * θ l) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [integral_mul_const, GaussianAlgebraFourth.coordinate_mixed_fourth]
      simp only [GaussianPairings.delta]
      split_ifs <;>
        simp only [zero_mul, mul_zero, one_mul, add_mul, map_zero, map_add,
          add_zero, zero_add]
    _ = _ := congrArg L (GaussianPairings.fourth_pairing θ)

/-- A pointwise sign survives the quadratic Gaussian average. -/
theorem sum_squares_nonneg (L : S →ₗ[ℝ] ℝ) (θ : ι → S)
    (h : ∀ t : ι → ℝ, 0 ≤ L (combination θ t ^ 2)) :
    0 ≤ L (∑ i, θ i ^ 2) := by
  rw [← integral_square L θ]
  exact integral_nonneg h

/-- The fourth average handles mixed products of the squares. -/
theorem squared_sum_squares_nonneg (L : S →ₗ[ℝ] ℝ) (θ : ι → S)
    (h : ∀ t : ι → ℝ, 0 ≤ L (combination θ t ^ 4)) :
    0 ≤ L ((∑ i, θ i ^ 2) ^ 2) := by
  have hi : 0 ≤ ∫ t : ι → ℝ, L (combination θ t ^ 4) ∂standardMeasure :=
    integral_nonneg h
  rw [integral_fourth L θ] at hi
  have he : L (3 * (∑ i, θ i ^ 2) ^ 2) = 3 * L ((∑ i, θ i ^ 2) ^ 2) := by
    rw [show (3 : S) * (∑ i, θ i ^ 2) ^ 2 = (3 : ℝ) • (∑ i, θ i ^ 2) ^ 2 by
      rw [Algebra.smul_def, map_ofNat]]
    exact L.map_smul _ _
  rw [he] at hi
  linarith

end
end QuaternionicSymmetry.GaussianFunctional
