import QuaternionicSymmetry.UnitaryProjectionMixedMoments
import QuaternionicSymmetry.ExchangeableCubic

/-! The explicit cubic rank-two Haar projection formula for diagonal matrices. -/

namespace QuaternionicSymmetry.UnitaryProjectionCubic

open Matrix MeasureTheory UnitaryProjectionDiagonal UnitaryProjectionMixedMoments
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def sameCoefficient (r : ℝ) : ℝ := 24 / (r * (r + 1) * (r + 2))
def pairCoefficient (r : ℝ) : ℝ := 12 / ((r - 1) * (r + 1) * (r + 2))
def distinctCoefficient (r : ℝ) : ℝ := 4 * (2 * r + 1) / (r * (r - 1) * (r + 1) * (r + 2))

theorem integral_product_pattern (s : Finset κ) (hs : s.card = 2)
    (hr : 3 ≤ Fintype.card κ) (i j k : κ) :
    let a := sameCoefficient (Fintype.card κ)
    let b := pairCoefficient (Fintype.card κ)
    let c := distinctCoefficient (Fintype.card κ)
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j * entry s U k
      ∂UnitaryHaarMeasure.probability) =
      c + (if i = j then b - c else 0) + (if i = k then b - c else 0) +
        (if j = k then b - c else 0) +
        (if i = j ∧ j = k then a - 3 * b + 2 * c else 0) := by
  dsimp only
  have hr₂ : 2 ≤ Fintype.card κ := by omega
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp only [if_true, and_self]
      have he (U : Matrix.unitaryGroup κ ℂ) :
          entry s U i * entry s U i * entry s U i = entry s U i ^ 3 := by ring
      simp_rw [he]
      rw [integral_entry_cube, hs]
      norm_num only [Nat.cast_ofNat]
      unfold sameCoefficient
      ring
    · simp only [hik, if_false, if_true, true_and, add_zero]
      simp_rw [← pow_two]
      rw [rank_two_sq_mul s hs hr₂ i k hik]
      unfold pairCoefficient
      ring
  · by_cases hik : i = k
    · subst k
      simp only [hij, Ne.symm hij, if_false, if_true, false_and, add_zero]
      have he (U : Matrix.unitaryGroup κ ℂ) :
          entry s U i * entry s U j * entry s U i = entry s U i ^ 2 * entry s U j := by ring
      simp_rw [he]
      rw [rank_two_sq_mul s hs hr₂ i j hij]
      unfold pairCoefficient
      ring
    · by_cases hjk : j = k
      · subst k
        simp only [hij, if_false, if_true, false_and, add_zero]
        have he (U : Matrix.unitaryGroup κ ℂ) :
            entry s U i * entry s U j * entry s U j = entry s U j ^ 2 * entry s U i := by ring
        simp_rw [he]
        rw [rank_two_sq_mul s hs hr₂ j i (Ne.symm hij)]
        unfold pairCoefficient
        ring
      · simp only [hij, hik, hjk, if_false, false_and, add_zero]
        exact rank_two_triple s hs hr i j k hij hik hjk

theorem integral_weighted_cube_expansion (s : Finset κ) (y : κ → ℝ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, (∑ i, y i * entry s U i) ^ 3
      ∂UnitaryHaarMeasure.probability) =
    ∑ i, ∑ j, ∑ k, y i * y j * y k *
      (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j * entry s U k
        ∂UnitaryHaarMeasure.probability) := by
  simp_rw [ExchangeableCubic.cube_sum]
  let F := fun (i j k : κ) (U : Matrix.unitaryGroup κ ℂ) =>
    y i * y j * y k * (entry s U i * entry s U j * entry s U k)
  have hc (i j k : κ) : Continuous (F i j k) :=
    continuous_const.mul (((continuous_entry s i).mul (continuous_entry s j)).mul
      (continuous_entry s k))
  have hi (i j : κ) : Continuous (fun U => ∑ k, F i j k U) :=
    continuous_finset_sum _ (fun k _ => hc i j k)
  have hj (i : κ) : Continuous (fun U => ∑ j, ∑ k, F i j k U) :=
    continuous_finset_sum _ (fun j _ => hi i j)
  change (∫ U, ∑ i, ∑ j, ∑ k, F i j k U ∂UnitaryHaarMeasure.probability) = _
  rw [integral_finset_sum _ (fun i _ => continuous_integrable (hj i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => continuous_integrable (hi i j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum _ (fun k _ => continuous_integrable (hc i j k))]
  apply Finset.sum_congr rfl
  intro k _
  exact integral_const_mul _ _

theorem integral_weighted_cube (s : Finset κ) (hs : s.card = 2)
    (hr : 3 ≤ Fintype.card κ) (y : κ → ℝ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, (∑ i, y i * entry s U i) ^ 3
      ∂UnitaryHaarMeasure.probability) =
    4 * ((2 * (Fintype.card κ : ℝ) + 1) * (∑ i, y i) ^ 3 +
      3 * (Fintype.card κ - 1) * (∑ i, y i) * (∑ i, y i ^ 2) +
      (Fintype.card κ - 4) * (∑ i, y i ^ 3)) /
      ((Fintype.card κ : ℝ) * (Fintype.card κ - 1) * (Fintype.card κ + 1) *
        (Fintype.card κ + 2)) := by
  rw [integral_weighted_cube_expansion]
  simp_rw [integral_product_pattern s hs hr]
  rw [ExchangeableCubic.sum_pattern]
  unfold sameCoefficient pairCoefficient distinctCoefficient
  have hr' : (3 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hr
  have h₀ : (Fintype.card κ : ℝ) ≠ 0 := by linarith
  have h₁ : (Fintype.card κ : ℝ) - 1 ≠ 0 := by linarith
  have hp : (Fintype.card κ : ℝ) + 1 ≠ 0 := by linarith
  have hp₂ : (Fintype.card κ : ℝ) + 2 ≠ 0 := by linarith
  field_simp
  ring

end
end QuaternionicSymmetry.UnitaryProjectionCubic
