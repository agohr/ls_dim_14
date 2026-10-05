import QuaternionicSymmetry.CharacterSeries
import Mathlib.Tactic

/-!
The virtual `Sp(1)` characters and the required even Taylor coefficients in
quaternionic dimensions 11–14.  Every identity is in the Laurent polynomial
ring or follows through the existing formal-series substitution.
-/

namespace QuaternionicSymmetry.HigherCharacters

open LaurentPolynomial
open Characters

noncomputable section

theorem virtual_eleven :
    virtual 11 = chi 13 - 12 * chi 11 + 65 * chi 9 - 208 * chi 7 +
      429 * chi 5 - 572 * chi 3 + 429 * chi 1 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring

theorem virtual_twelve :
    virtual 12 = chi 14 - 15 * chi 12 + 105 * chi 10 - 455 * chi 8 +
      1365 * chi 6 - 3003 * chi 4 + 5005 * chi 2 - 6435 * chi 0 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring

theorem virtual_thirteen :
    virtual 13 = chi 15 - 14 * chi 13 + 90 * chi 11 - 350 * chi 9 +
      910 * chi 7 - 1638 * chi 5 + 2002 * chi 3 - 1430 * chi 1 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring

theorem virtual_fourteen :
    virtual 14 = chi 16 - 17 * chi 14 + 136 * chi 12 - 680 * chi 10 +
      2380 * chi 8 - 6188 * chi 6 + 12376 * chi 4 - 19448 * chi 2 +
      24310 * chi 0 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring

theorem taylor_eleven :
    (List.range 12).map (fun j => taylorCoefficient j (virtual 11)) =
      [0, 0, 0, 0, 0, 0, 8192, 20480, 121856 / 5, 3492352 / 189,
        6796864 / 675, 46368 / 11] := by
  rw [virtual_eleven]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h12 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (12 * p) = (12 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 12 p
  have h65 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (65 * p) = (65 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 65 p
  have h208 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (208 * p) = (208 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 208 p
  have h429 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (429 * p) = (429 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 429 p
  have h572 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (572 * p) = (572 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 572 p
  simp only [h12, h65, h208, h429, h572]
  norm_num [Nat.factorial]


theorem taylor_twelve :
    (List.range 13).map (fun j => taylorCoefficient j (virtual 12)) =
      [0, 0, 0, 0, 0, 0, 0, 16384, 114688 / 3, 1949696 / 45, 4292608 / 135, 34422784 / 2025, 2097152 / 297] := by
  rw [virtual_twelve]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h15 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (15 * p) = (15 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 15 p
  have h105 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (105 * p) = (105 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 105 p
  have h455 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (455 * p) = (455 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 455 p
  have h1365 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (1365 * p) = (1365 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 1365 p
  have h3003 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (3003 * p) = (3003 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 3003 p
  have h5005 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (5005 * p) = (5005 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 5005 p
  have h6435c (j : ℕ) :
      taylorCoefficient j (6435 : LaurentPolynomial ℚ) =
        (6435 : ℚ) * ((0 : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ)) := by
    exact taylorCoefficient_natCast j 6435
  simp only [h15, h105, h455, h1365, h3003, h5005, h6435c]
  norm_num [Nat.factorial]


theorem taylor_thirteen :
    (List.range 14).map (fun j => taylorCoefficient j (virtual 13)) =
      [0, 0, 0, 0, 0, 0, 0, 32768, 278528 / 3, 5681152 / 45, 14870528 / 135, 985339136 / 14175, 70463872 / 2079, 134961308128 / 10135125] := by
  rw [virtual_thirteen]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h14 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (14 * p) = (14 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 14 p
  have h90 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (90 * p) = (90 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 90 p
  have h350 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (350 * p) = (350 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 350 p
  have h910 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (910 * p) = (910 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 910 p
  have h1638 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (1638 * p) = (1638 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 1638 p
  have h2002 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (2002 * p) = (2002 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 2002 p
  have h1430 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (1430 * p) = (1430 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 1430 p
  simp only [h14, h90, h350, h910, h1638, h2002, h1430]
  norm_num [Nat.factorial]


theorem taylor_fourteen :
    (List.range 15).map (fun j => taylorCoefficient j (virtual 14)) =
      [0, 0, 0, 0, 0, 0, 0, 0, 65536, 524288 / 3, 3407872 / 15, 181403648 / 945, 2490368 / 21, 989855744 / 17325, 2855653081088 / 127702575] := by
  rw [virtual_fourteen]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h17 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (17 * p) = (17 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 17 p
  have h136 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (136 * p) = (136 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 136 p
  have h680 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (680 * p) = (680 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 680 p
  have h2380 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (2380 * p) = (2380 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 2380 p
  have h6188 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (6188 * p) = (6188 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 6188 p
  have h12376 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (12376 * p) = (12376 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 12376 p
  have h19448 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (19448 * p) = (19448 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 19448 p
  have h24310c (j : ℕ) :
      taylorCoefficient j (24310 : LaurentPolynomial ℚ) =
        (24310 : ℚ) * ((0 : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ)) := by
    exact taylorCoefficient_natCast j 24310
  simp only [h17, h136, h680, h2380, h6188, h12376, h19448, h24310c]
  norm_num [Nat.factorial]


/-- The table is also the coefficient table of the actual formal exponential substitution. -/
theorem series_eleven :
    (List.range 12).map
      (fun j => PowerSeries.coeff (2 * j)
        (CharacterSeries.characterSeries (virtual 11))) =
      [0, 0, 0, 0, 0, 0, 8192, 20480, 121856 / 5, 3492352 / 189, 6796864 / 675, 46368 / 11] := by
  simpa only [CharacterSeries.coefficient_characterSeries] using taylor_eleven


/-- The table is also the coefficient table of the actual formal exponential substitution. -/
theorem series_twelve :
    (List.range 13).map
      (fun j => PowerSeries.coeff (2 * j)
        (CharacterSeries.characterSeries (virtual 12))) =
      [0, 0, 0, 0, 0, 0, 0, 16384, 114688 / 3, 1949696 / 45, 4292608 / 135, 34422784 / 2025, 2097152 / 297] := by
  simpa only [CharacterSeries.coefficient_characterSeries] using taylor_twelve


/-- The table is also the coefficient table of the actual formal exponential substitution. -/
theorem series_thirteen :
    (List.range 14).map
      (fun j => PowerSeries.coeff (2 * j)
        (CharacterSeries.characterSeries (virtual 13))) =
      [0, 0, 0, 0, 0, 0, 0, 32768, 278528 / 3, 5681152 / 45, 14870528 / 135, 985339136 / 14175, 70463872 / 2079, 134961308128 / 10135125] := by
  simpa only [CharacterSeries.coefficient_characterSeries] using taylor_thirteen


/-- The table is also the coefficient table of the actual formal exponential substitution. -/
theorem series_fourteen :
    (List.range 15).map
      (fun j => PowerSeries.coeff (2 * j)
        (CharacterSeries.characterSeries (virtual 14))) =
      [0, 0, 0, 0, 0, 0, 0, 0, 65536, 524288 / 3, 3407872 / 15, 181403648 / 945, 2490368 / 21, 989855744 / 17325, 2855653081088 / 127702575] := by
  simpa only [CharacterSeries.coefficient_characterSeries] using taylor_fourteen

theorem taylor_eleven_coeff (j : Fin 12) :
    taylorCoefficient j (virtual 11) =
      ([0, 0, 0, 0, 0, 0, 8192, 20480, 121856 / 5, 3492352 / 189,
        6796864 / 675, 46368 / 11] : List ℚ).get j := by
  have h := congrArg (fun l : List ℚ => l[j.val]?) taylor_eleven
  simpa [List.getElem?_map, List.getElem_range, j.isLt] using h

/-- The first possible term in dimension eleven has weight six. -/
theorem taylor_eleven_below_six (j : ℕ) (hj : j < 6) :
    taylorCoefficient j (virtual 11) = 0 := by
  have h := congrArg (fun l : List ℚ => l[j]?) taylor_eleven
  interval_cases j <;>
    simpa [List.getElem?_map, List.getElem_range] using h


theorem taylor_twelve_coeff (j : Fin 13) :
    taylorCoefficient j (virtual 12) =
      ([0, 0, 0, 0, 0, 0, 0, 16384, 114688 / 3, 1949696 / 45, 4292608 / 135, 34422784 / 2025, 2097152 / 297] : List ℚ).get j := by
  have h := congrArg (fun l : List ℚ => l[j.val]?) taylor_twelve
  simpa [List.getElem?_map, List.getElem_range, j.isLt] using h

/-- The first possible term in dimension 12 has weight 7. -/
theorem taylor_twelve_below_7 (j : ℕ) (hj : j < 7) :
    taylorCoefficient j (virtual 12) = 0 := by
  have h := congrArg (fun l : List ℚ => l[j]?) taylor_twelve
  interval_cases j <;>
    simpa [List.getElem?_map, List.getElem_range] using h


theorem taylor_thirteen_coeff (j : Fin 14) :
    taylorCoefficient j (virtual 13) =
      ([0, 0, 0, 0, 0, 0, 0, 32768, 278528 / 3, 5681152 / 45, 14870528 / 135, 985339136 / 14175, 70463872 / 2079, 134961308128 / 10135125] : List ℚ).get j := by
  have h := congrArg (fun l : List ℚ => l[j.val]?) taylor_thirteen
  simpa [List.getElem?_map, List.getElem_range, j.isLt] using h

/-- The first possible term in dimension 13 has weight 7. -/
theorem taylor_thirteen_below_7 (j : ℕ) (hj : j < 7) :
    taylorCoefficient j (virtual 13) = 0 := by
  have h := congrArg (fun l : List ℚ => l[j]?) taylor_thirteen
  interval_cases j <;>
    simpa [List.getElem?_map, List.getElem_range] using h


theorem taylor_fourteen_coeff (j : Fin 15) :
    taylorCoefficient j (virtual 14) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 65536, 524288 / 3, 3407872 / 15, 181403648 / 945, 2490368 / 21, 989855744 / 17325, 2855653081088 / 127702575] : List ℚ).get j := by
  have h := congrArg (fun l : List ℚ => l[j.val]?) taylor_fourteen
  simpa [List.getElem?_map, List.getElem_range, j.isLt] using h

/-- The first possible term in dimension 14 has weight 8. -/
theorem taylor_fourteen_below_8 (j : ℕ) (hj : j < 8) :
    taylorCoefficient j (virtual 14) = 0 := by
  have h := congrArg (fun l : List ℚ => l[j]?) taylor_fourteen
  interval_cases j <;>
    simpa [List.getElem?_map, List.getElem_range] using h

private theorem truncate_convolution {R : Type*} [AddCommMonoid R] [Module ℚ R]
    (n k : ℕ) (hk : k ≤ n + 1) (w : ℕ → ℚ) (A : ℕ → R)
    (hw : ∀ j < k, w j = 0) :
    (∑ j ∈ Finset.range (n + 1), w (n - j) • A j) =
      ∑ j ∈ Finset.range (n + 1 - k), w (n - j) • A j := by
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j hj hnot
    have hjfull : j < n + 1 := Finset.mem_range.mp hj
    have hjtail : n + 1 - k ≤ j := by
      simpa only [Finset.mem_range, not_lt] using hnot
    have hvanish : n - j < k := by omega
    simp [hw (n - j) hvanish]

/-- In dimension eleven only `A₀` through `A₅` enter the reduced density. -/
theorem convolution_eleven {R : Type*} [AddCommMonoid R] [Module ℚ R]
    (A : ℕ → R) :
    (∑ j ∈ Finset.range 12, taylorCoefficient (11 - j) (virtual 11) • A j) =
      ∑ j ∈ Finset.range 6, taylorCoefficient (11 - j) (virtual 11) • A j := by
  simpa using truncate_convolution 11 6 (by omega)
    (fun j => taylorCoefficient j (virtual 11)) A taylor_eleven_below_six

/-- In dimension twelve only `A₀` through `A₅` enter the reduced density. -/
theorem convolution_twelve {R : Type*} [AddCommMonoid R] [Module ℚ R]
    (A : ℕ → R) :
    (∑ j ∈ Finset.range 13, taylorCoefficient (12 - j) (virtual 12) • A j) =
      ∑ j ∈ Finset.range 6, taylorCoefficient (12 - j) (virtual 12) • A j := by
  simpa using truncate_convolution 12 7 (by omega)
    (fun j => taylorCoefficient j (virtual 12)) A taylor_twelve_below_7

/-- In dimension thirteen only `A₀` through `A₆` enter the reduced density. -/
theorem convolution_thirteen {R : Type*} [AddCommMonoid R] [Module ℚ R]
    (A : ℕ → R) :
    (∑ j ∈ Finset.range 14, taylorCoefficient (13 - j) (virtual 13) • A j) =
      ∑ j ∈ Finset.range 7, taylorCoefficient (13 - j) (virtual 13) • A j := by
  simpa using truncate_convolution 13 7 (by omega)
    (fun j => taylorCoefficient j (virtual 13)) A taylor_thirteen_below_7

/-- In dimension fourteen only `A₀` through `A₆` enter the reduced density. -/
theorem convolution_fourteen {R : Type*} [AddCommMonoid R] [Module ℚ R]
    (A : ℕ → R) :
    (∑ j ∈ Finset.range 15, taylorCoefficient (14 - j) (virtual 14) • A j) =
      ∑ j ∈ Finset.range 7, taylorCoefficient (14 - j) (virtual 14) • A j := by
  simpa using truncate_convolution 14 8 (by omega)
    (fun j => taylorCoefficient j (virtual 14)) A taylor_fourteen_below_8

end
end QuaternionicSymmetry.HigherCharacters
