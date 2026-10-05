import QuaternionicSymmetry.UnitaryProjectionDiagonal

/-! Mixed diagonal moments of Haar projections follow from exchangeability
and the deterministic trace, with all scalar integrals justified. -/

namespace QuaternionicSymmetry.UnitaryProjectionMixedMoments

open Matrix MeasureTheory UnitaryProjectionDiagonal
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem integral_pow_mul_swap (s : Finset κ) (i j a : κ)
    (hij : i ≠ j) (hia : i ≠ a) (m : ℕ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ m * entry s U a
      ∂UnitaryHaarMeasure.probability) =
    ∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ m * entry s U j
      ∂UnitaryHaarMeasure.probability := by
  simpa only [Equiv.swap_apply_of_ne_of_ne hij hia, Equiv.swap_apply_left] using
    integral_permute s (Equiv.swap j a) (fun x => x i ^ m * x j)

theorem pow_mul_trace_relation (s : Finset κ) (i j : κ) (hij : i ≠ j) (m : ℕ) :
    ((Fintype.card κ : ℝ) - 1) *
      (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ m * entry s U j
        ∂UnitaryHaarMeasure.probability) =
    (s.card : ℝ) * (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ m
      ∂UnitaryHaarMeasure.probability) -
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ (m + 1)
      ∂UnitaryHaarMeasure.probability) := by
  let b := ∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ m * entry s U j
    ∂UnitaryHaarMeasure.probability
  let d := ∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ (m + 1)
    ∂UnitaryHaarMeasure.probability
  have he (a : κ) :
      (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ m * entry s U a
        ∂UnitaryHaarMeasure.probability) = b + if a = i then d - b else 0 := by
    by_cases h : a = i
    · subst a
      simp only [if_true, add_sub_cancel]
      simp only [d, pow_succ]
    · simp only [h, if_false, add_zero]
      exact integral_pow_mul_swap s i j a hij (Ne.symm h) m
  have ht : (∑ a, ∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ m * entry s U a
      ∂UnitaryHaarMeasure.probability) =
      (s.card : ℝ) * (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ m
        ∂UnitaryHaarMeasure.probability) := by
    rw [← integral_finset_sum Finset.univ
      (f := fun a U => entry s U i ^ m * entry s U a) (fun a _ => continuous_integrable
      (((continuous_entry s i).pow m).mul (continuous_entry s a)))]
    simp_rw [← Finset.mul_sum, sum_entry]
    rw [integral_mul_const, mul_comm]
  simp_rw [he] at ht
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at ht
  change ((Fintype.card κ : ℝ) - 1) * b = _ - d
  linarith

theorem integral_triple_swap (s : Finset κ) (i j k a : κ)
    (hik : i ≠ k) (hia : i ≠ a) (hjk : j ≠ k) (hja : j ≠ a) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j * entry s U a
      ∂UnitaryHaarMeasure.probability) =
    ∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j * entry s U k
      ∂UnitaryHaarMeasure.probability := by
  simpa only [Equiv.swap_apply_of_ne_of_ne hik hia,
    Equiv.swap_apply_of_ne_of_ne hjk hja, Equiv.swap_apply_left] using
    integral_permute s (Equiv.swap k a) (fun x => x i * x j * x k)

theorem triple_trace_relation (s : Finset κ) (i j k : κ)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((Fintype.card κ : ℝ) - 2) *
      (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j * entry s U k
        ∂UnitaryHaarMeasure.probability) =
    (s.card : ℝ) * (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j
      ∂UnitaryHaarMeasure.probability) -
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ 2 * entry s U j
      ∂UnitaryHaarMeasure.probability) -
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U j ^ 2 * entry s U i
      ∂UnitaryHaarMeasure.probability) := by
  let c := ∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j * entry s U k
    ∂UnitaryHaarMeasure.probability
  let b₁ := ∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ 2 * entry s U j
    ∂UnitaryHaarMeasure.probability
  let b₂ := ∫ U : Matrix.unitaryGroup κ ℂ, entry s U j ^ 2 * entry s U i
    ∂UnitaryHaarMeasure.probability
  have he (a : κ) :
      (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j * entry s U a
        ∂UnitaryHaarMeasure.probability) =
        c + (if a = i then b₁ - c else 0) + (if a = j then b₂ - c else 0) := by
    by_cases hai : a = i
    · subst a
      simp only [hij, if_false, if_true, add_sub_cancel, add_zero]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun U => by ring
    · by_cases haj : a = j
      · subst a
        simp only [hij.symm, if_false, if_true, add_zero, add_sub_cancel]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun U => by ring
      · simp only [hai, haj, if_false, add_zero]
        exact integral_triple_swap s i j k a hik (Ne.symm hai) hjk (Ne.symm haj)
  have ht : (∑ a, ∫ U : Matrix.unitaryGroup κ ℂ,
      entry s U i * entry s U j * entry s U a ∂UnitaryHaarMeasure.probability) =
      (s.card : ℝ) * (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j
        ∂UnitaryHaarMeasure.probability) := by
    rw [← integral_finset_sum Finset.univ
      (f := fun a U => entry s U i * entry s U j * entry s U a) (fun a _ => continuous_integrable
      (((continuous_entry s i).mul (continuous_entry s j)).mul (continuous_entry s a)))]
    simp_rw [← Finset.mul_sum, sum_entry]
    rw [integral_mul_const, mul_comm]
  simp_rw [he] at ht
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at ht
  change ((Fintype.card κ : ℝ) - 2) * c = _ - b₁ - b₂
  linarith

theorem rank_two_pair (s : Finset κ) (hs : s.card = 2)
    (hr : 2 ≤ Fintype.card κ) (i j : κ) (hij : i ≠ j) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j
      ∂UnitaryHaarMeasure.probability) =
      2 * (2 * (Fintype.card κ : ℝ) - 1) /
        ((Fintype.card κ : ℝ) * (Fintype.card κ - 1) * (Fintype.card κ + 1)) := by
  have hr' : (2 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hr
  have h₀ : (Fintype.card κ : ℝ) ≠ 0 := by linarith
  have h₁ : (Fintype.card κ : ℝ) - 1 ≠ 0 := by linarith
  have hp : (Fintype.card κ : ℝ) + 1 ≠ 0 := by linarith
  apply mul_left_cancel₀ h₁
  have h := pow_mul_trace_relation s i j hij 1
  simp only [pow_one, Nat.reduceAdd, integral_entry, integral_entry_sq, hs,
    Nat.cast_ofNat] at h
  rw [h]
  field_simp
  ring

theorem rank_two_sq_mul (s : Finset κ) (hs : s.card = 2)
    (hr : 2 ≤ Fintype.card κ) (i j : κ) (hij : i ≠ j) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ 2 * entry s U j
      ∂UnitaryHaarMeasure.probability) =
      12 / (((Fintype.card κ : ℝ) - 1) * (Fintype.card κ + 1) *
        (Fintype.card κ + 2)) := by
  have hr' : (2 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hr
  have h₀ : (Fintype.card κ : ℝ) ≠ 0 := by linarith
  have h₁ : (Fintype.card κ : ℝ) - 1 ≠ 0 := by linarith
  have hp : (Fintype.card κ : ℝ) + 1 ≠ 0 := by linarith
  have hp₂ : (Fintype.card κ : ℝ) + 2 ≠ 0 := by linarith
  apply mul_left_cancel₀ h₁
  rw [pow_mul_trace_relation s i j hij 2]
  norm_num only [Nat.reduceAdd, integral_entry_sq, integral_entry_cube, hs, Nat.cast_ofNat]
  field_simp
  ring

theorem rank_two_triple (s : Finset κ) (hs : s.card = 2)
    (hr : 3 ≤ Fintype.card κ) (i j k : κ) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j * entry s U k
      ∂UnitaryHaarMeasure.probability) =
      4 * (2 * (Fintype.card κ : ℝ) + 1) /
        ((Fintype.card κ : ℝ) * (Fintype.card κ - 1) * (Fintype.card κ + 1) *
          (Fintype.card κ + 2)) := by
  have hr₂ : 2 ≤ Fintype.card κ := by omega
  have hr' : (3 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hr
  have h₀ : (Fintype.card κ : ℝ) ≠ 0 := by linarith
  have h₁ : (Fintype.card κ : ℝ) - 1 ≠ 0 := by linarith
  have h₂ : (Fintype.card κ : ℝ) - 2 ≠ 0 := by linarith
  have hp : (Fintype.card κ : ℝ) + 1 ≠ 0 := by linarith
  have hp₂ : (Fintype.card κ : ℝ) + 2 ≠ 0 := by linarith
  apply mul_left_cancel₀ h₂
  rw [triple_trace_relation s i j k hij hik hjk, rank_two_pair s hs hr₂ i j hij,
    rank_two_sq_mul s hs hr₂ i j hij, rank_two_sq_mul s hs hr₂ j i hij.symm, hs]
  field_simp
  ring

end
end QuaternionicSymmetry.UnitaryProjectionMixedMoments
