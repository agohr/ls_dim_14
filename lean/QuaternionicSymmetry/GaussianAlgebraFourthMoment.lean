import QuaternionicSymmetry.GaussianAlgebraFourth
import QuaternionicSymmetry.GaussianPairings

/-! The fourth Wick identity in a complete normed commutative real algebra. -/

namespace QuaternionicSymmetry.GaussianAlgebraFourthMoment

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

variable {ι S : Type*} [Fintype ι] [DecidableEq ι]
  [NormedCommRing S] [NormedAlgebra ℝ S] [CompleteSpace S]

abbrev standardMeasure : Measure (ι → ℝ) := GaussianAlgebra.standardMeasure

omit [CompleteSpace S] in
private theorem fourfold_integrable (i j k l : ι) (θ : ι → S) :
    Integrable (fun ω : ι → ℝ ↦
      (ω i * ω j * ω k * ω l) • (θ i * θ j * θ k * θ l)) standardMeasure :=
  (GaussianAlgebraFourth.coordinate_mixed_fourth_integrable i j k l).smul_const _

/-- The fourth Wick identity for a finite algebra-valued Gaussian combination. -/
theorem integral_combination_fourth (θ : ι → S) :
    (∫ ω : ι → ℝ, GaussianAlgebra.combination θ ω ^ 4 ∂standardMeasure) =
      3 * (∑ i, θ i ^ 2) ^ 2 := by
  rw [show (fun ω : ι → ℝ ↦ GaussianAlgebra.combination θ ω ^ 4) =
      fun ω ↦ ∑ i, ∑ j, ∑ k, ∑ l,
        (ω i * ω j * ω k * ω l) • (θ i * θ j * θ k * θ l) by
    ext ω
    simp only [GaussianAlgebra.combination, pow_succ, pow_zero, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    simp only [one_mul]
    simp only [Algebra.smul_def, map_mul]
    ring]
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        ∫ ω : ι → ℝ, (ω i * ω j * ω k * ω l) • (θ i * θ j * θ k * θ l)
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
            rw [integral_finset_sum]
            · intro l _
              exact fourfold_integrable i j k l θ
          · intro k _
            exact integrable_finset_sum _ fun l _ ↦ fourfold_integrable i j k l θ
        · intro j _
          exact integrable_finset_sum _ fun k _ ↦
            integrable_finset_sum _ fun l _ ↦ fourfold_integrable i j k l θ
      · intro i _
        exact integrable_finset_sum _ fun j _ ↦
          integrable_finset_sum _ fun k _ ↦
            integrable_finset_sum _ fun l _ ↦ fourfold_integrable i j k l θ
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        (GaussianPairings.delta i j * GaussianPairings.delta k l +
          GaussianPairings.delta i k * GaussianPairings.delta j l +
          GaussianPairings.delta i l * GaussianPairings.delta j k) *
          θ i * θ j * θ k * θ l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [integral_smul_const, GaussianAlgebraFourth.coordinate_mixed_fourth]
      simp only [GaussianPairings.delta]
      split_ifs <;> simp [Algebra.smul_def]
      all_goals ring
    _ = _ := GaussianPairings.fourth_pairing θ

end
end QuaternionicSymmetry.GaussianAlgebraFourthMoment
