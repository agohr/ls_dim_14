import QuaternionicSymmetry.UnitaryProjectionCubic

/-! Cubic Haar projection moments for every projection rank. -/
namespace QuaternionicSymmetry.UnitaryProjectionGeneralCubic

open Matrix MeasureTheory UnitaryProjectionDiagonal UnitaryProjectionMixedMoments
open scoped BigOperators
noncomputable section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def sameCoefficient (r ell : ℝ) : ℝ := ell * (ell + 1) * (ell + 2) / (r * (r + 1) * (r + 2))
def pairMoment (r ell : ℝ) : ℝ := (ell * (ell / r) - ell * (ell + 1) / (r * (r + 1))) / (r - 1)
def pairCoefficient (r ell : ℝ) : ℝ :=
  (ell * (ell * (ell + 1) / (r * (r + 1))) - sameCoefficient r ell) / (r - 1)
def distinctCoefficient (r ell : ℝ) : ℝ :=
  (ell * pairMoment r ell - 2 * pairCoefficient r ell) / (r - 2)

theorem integral_pair (s : Finset κ) (hr : 2 ≤ Fintype.card κ)
    (i j : κ) (hij : i ≠ j) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j
      ∂UnitaryHaarMeasure.probability) = pairMoment (Fintype.card κ) s.card := by
  have hr' : (2 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hr
  have hd : (Fintype.card κ : ℝ) - 1 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  have h := pow_mul_trace_relation s i j hij 1
  simpa only [pow_one, Nat.reduceAdd, integral_entry, integral_entry_sq, mul_comm,
    pairMoment] using h

theorem integral_sq_mul (s : Finset κ) (hr : 2 ≤ Fintype.card κ)
    (i j : κ) (hij : i ≠ j) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i ^ 2 * entry s U j
      ∂UnitaryHaarMeasure.probability) = pairCoefficient (Fintype.card κ) s.card := by
  have hr' : (2 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hr
  have hd : (Fintype.card κ : ℝ) - 1 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  have h := pow_mul_trace_relation s i j hij 2
  simpa only [Nat.reduceAdd, integral_entry_sq, integral_entry_cube, mul_comm,
    sameCoefficient] using h

theorem integral_triple (s : Finset κ) (hr : 3 ≤ Fintype.card κ)
    (i j k : κ) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ U : Matrix.unitaryGroup κ ℂ, entry s U i * entry s U j * entry s U k
      ∂UnitaryHaarMeasure.probability) = distinctCoefficient (Fintype.card κ) s.card := by
  have hr' : (3 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hr
  have hd : (Fintype.card κ : ℝ) - 2 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  have h := triple_trace_relation s i j k hij hik hjk
  rw [integral_pair s (by omega) i j hij, integral_sq_mul s (by omega) i j hij,
    integral_sq_mul s (by omega) j i hij.symm] at h
  linarith

theorem integral_product_pattern (s : Finset κ)
    (hr : 3 ≤ Fintype.card κ) (i j k : κ) :
    let a := sameCoefficient (Fintype.card κ) s.card
    let b := pairCoefficient (Fintype.card κ) s.card
    let c := distinctCoefficient (Fintype.card κ) s.card
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
      rw [integral_entry_cube]
      unfold sameCoefficient
      ring
    · simp only [hik, if_false, if_true, true_and, add_zero]
      simp_rw [← pow_two]
      rw [integral_sq_mul s hr₂ i k hik]
      unfold pairCoefficient
      ring
  · by_cases hik : i = k
    · subst k
      simp only [hij, Ne.symm hij, if_false, if_true, false_and, add_zero]
      have he (U : Matrix.unitaryGroup κ ℂ) :
          entry s U i * entry s U j * entry s U i = entry s U i ^ 2 * entry s U j := by ring
      simp_rw [he]
      rw [integral_sq_mul s hr₂ i j hij]
      unfold pairCoefficient
      ring
    · by_cases hjk : j = k
      · subst k
        simp only [hij, if_false, if_true, false_and, add_zero]
        have he (U : Matrix.unitaryGroup κ ℂ) :
            entry s U i * entry s U j * entry s U j = entry s U j ^ 2 * entry s U i := by ring
        simp_rw [he]
        rw [integral_sq_mul s hr₂ j i (Ne.symm hij)]
        unfold pairCoefficient
        ring
      · simp only [hij, hik, hjk, if_false, false_and, add_zero]
        exact integral_triple s hr i j k hij hik hjk

theorem integral_weighted_cube (s : Finset κ) (hr : 3 ≤ Fintype.card κ)
    (y : κ → ℝ) :
    (∫ U : Matrix.unitaryGroup κ ℂ, (∑ i, y i * entry s U i) ^ 3
      ∂UnitaryHaarMeasure.probability) =
      distinctCoefficient (Fintype.card κ) s.card * (∑ i, y i) ^ 3 +
      3 * (pairCoefficient (Fintype.card κ) s.card - distinctCoefficient (Fintype.card κ) s.card) *
        (∑ i, y i) * (∑ i, y i ^ 2) +
      (sameCoefficient (Fintype.card κ) s.card - 3 * pairCoefficient (Fintype.card κ) s.card +
        2 * distinctCoefficient (Fintype.card κ) s.card) * (∑ i, y i ^ 3) := by
  rw [UnitaryProjectionCubic.integral_weighted_cube_expansion]
  simp_rw [integral_product_pattern s hr]
  exact ExchangeableCubic.sum_pattern y _ _ _

end
end QuaternionicSymmetry.UnitaryProjectionGeneralCubic
