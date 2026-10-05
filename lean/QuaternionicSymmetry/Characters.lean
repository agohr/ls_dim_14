import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-!
The finite Laurent character calculations of Chapter 9.
These are identities in the actual Laurent polynomial ring over ℚ.
No index theorem or representation-theoretic classification is assumed.
-/

namespace QuaternionicSymmetry.Characters

open LaurentPolynomial

noncomputable section

/-- The explicitly displayed torus character of `Sym^q H`. -/
def chi (q : ℕ) : LaurentPolynomial ℚ :=
  ∑ j ∈ Finset.range (q + 1), T ((q : ℤ) - 2 * (j : ℤ))

/-- Chapter 9's virtual Laurent character. -/
def virtual (n : ℕ) : LaurentPolynomial ℚ :=
  if n % 2 = 0 then (T 1 - T (-1)) ^ (n + 2)
  else (T 1 - T (-1)) ^ (n + 1) * (T 1 + T (-1))

/-- Algebraic coefficient of `h^(2*j)` after formally replacing `T^m` by `exp(m*h)`.
This definition is a finite sum; no analytic convergence is used. -/
def taylorCoefficient (j : ℕ) : LaurentPolynomial ℚ →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (fun m : ℤ => (m : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ))

@[simp] theorem taylorCoefficient_T (j : ℕ) (m : ℤ) :
    taylorCoefficient j (T m) = (m : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ) := by
  change Finsupp.linearCombination ℚ
      (fun m : ℤ => (m : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ))
      (Finsupp.single m 1) = _
  rw [Finsupp.linearCombination_single]
  simp

@[simp] theorem taylorCoefficient_one (j : ℕ) :
    taylorCoefficient j 1 = (0 : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ) := by
  simpa only [T_zero, Int.cast_zero] using taylorCoefficient_T j 0

@[simp] theorem taylorCoefficient_nat_mul (j n : ℕ) (p : LaurentPolynomial ℚ) :
    taylorCoefficient j ((n : LaurentPolynomial ℚ) * p) =
      (n : ℚ) * taylorCoefficient j p := by
  simpa only [nsmul_eq_mul] using map_nsmul (taylorCoefficient j).toAddMonoidHom n p

@[simp] theorem taylorCoefficient_natCast (j n : ℕ) :
    taylorCoefficient j (n : LaurentPolynomial ℚ) =
      (n : ℚ) * ((0 : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ)) := by
  simpa only [mul_one, taylorCoefficient_one] using taylorCoefficient_nat_mul j n 1

theorem virtual_two : virtual 2 = chi 4 - 5 * chi 2 + 10 * chi 0 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring


theorem virtual_3 : virtual 3 = chi 5 - 4 * chi 3 + 5 * chi 1 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring


theorem virtual_4 : virtual 4 = chi 6 - 7 * chi 4 + 21 * chi 2 - 35 * chi 0 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring


theorem virtual_5 : virtual 5 = chi 7 - 6 * chi 5 + 14 * chi 3 - 14 * chi 1 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring


theorem virtual_6 : virtual 6 = chi 8 - 9 * chi 6 + 36 * chi 4 - 84 * chi 2 + 126 * chi 0 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring


theorem virtual_7 : virtual 7 = chi 9 - 8 * chi 7 + 27 * chi 5 - 48 * chi 3 + 42 * chi 1 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring


theorem virtual_8 : virtual 8 = chi 10 - 11 * chi 8 + 55 * chi 6 - 165 * chi 4 + 330 * chi 2 - 462 * chi 0 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring


theorem virtual_9 : virtual 9 = chi 11 - 10 * chi 9 + 44 * chi 7 - 110 * chi 5 + 165 * chi 3 - 132 * chi 1 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring


theorem virtual_10 : virtual 10 = chi 12 - 13 * chi 10 + 78 * chi 8 - 286 * chi 6 + 715 * chi 4 - 1287 * chi 2 + 1716 * chi 0 := by
  norm_num [virtual, chi, Finset.sum_range_succ]
  ring_nf
  simp only [T_pow, ← T_add]
  norm_num
  ring


theorem taylor_two : (List.range 3).map (fun j => taylorCoefficient j (virtual 2)) =
    [0, 0, 16] := by
  rw [virtual_two]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_nat_mul, taylorCoefficient_natCast, taylorCoefficient_one,
    taylorCoefficient_T, Nat.factorial]
  have h5 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (5 * p) = (5 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 5 p
  rw [h5, h5, h5]
  have h10 (j : ℕ) :
      taylorCoefficient j (10 : LaurentPolynomial ℚ) =
        (10 : ℚ) * ((0 : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ)) := by
    exact taylorCoefficient_natCast j 10
  rw [h10, h10, h10]
  norm_num [Nat.factorial]

theorem taylor_three : (List.range 4).map (fun j => taylorCoefficient j (virtual 3)) =
    [0, 0, 32, 112 / 3] := by
  rw [virtual_3]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h4 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (4 * p) = (4 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 4 p
  have h5 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (5 * p) = (5 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 5 p
  rw [h4, h4, h4, h4, h5, h5, h5, h5]
  norm_num [Nat.factorial]

theorem taylor_four : (List.range 5).map (fun j => taylorCoefficient j (virtual 4)) =
    [0, 0, 0, 64, 64] := by
  rw [virtual_4]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h7 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (7 * p) = (7 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 7 p
  have h21 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (21 * p) = (21 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 21 p
  have h35 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (35 * p) = (35 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 35 p
  have h35c (j : ℕ) :
      taylorCoefficient j (35 : LaurentPolynomial ℚ) =
        (35 : ℚ) * ((0 : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ)) := by
    exact taylorCoefficient_natCast j 35
  rw [h7, h7, h7, h7, h7, h21, h21, h21, h21, h21,
    h35c, h35c, h35c, h35c, h35c]
  norm_num [Nat.factorial]

theorem taylor_five : (List.range 6).map (fun j => taylorCoefficient j (virtual 5)) =
    [0, 0, 0, 128, 192, 1936 / 15] := by
  rw [virtual_5]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h6 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (6 * p) = (6 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 6 p
  have h14 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (14 * p) = (14 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 14 p
  simp only [h6, h14]
  norm_num [Nat.factorial]

theorem taylor_six : (List.range 7).map (fun j => taylorCoefficient j (virtual 6)) =
    [0, 0, 0, 0, 256, 1024 / 3, 9728 / 45] := by
  rw [virtual_6]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h9 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (9 * p) = (9 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 9 p
  have h36 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (36 * p) = (36 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 36 p
  have h84 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (84 * p) = (84 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 84 p
  have h126c (j : ℕ) :
      taylorCoefficient j (126 : LaurentPolynomial ℚ) =
        (126 : ℚ) * ((0 : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ)) := by
    exact taylorCoefficient_natCast j 126
  simp only [h9, h36, h84, h126c]
  norm_num [Nat.factorial]

theorem taylor_seven : (List.range 8).map (fun j => taylorCoefficient j (virtual 7)) =
    [0, 0, 0, 0, 512, 2816 / 3, 35776 / 45, 79136 / 189] := by
  rw [virtual_7]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h8 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (8 * p) = (8 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 8 p
  have h27 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (27 * p) = (27 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 27 p
  have h48 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (48 * p) = (48 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 48 p
  have h42 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (42 * p) = (42 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 42 p
  simp only [h8, h27, h48, h42]
  norm_num [Nat.factorial]

theorem taylor_eight : (List.range 9).map (fun j => taylorCoefficient j (virtual 8)) =
    [0, 0, 0, 0, 0, 1024, 5120 / 3, 4096 / 3, 44032 / 63] := by
  rw [virtual_8]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h11 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (11 * p) = (11 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 11 p
  have h55 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (55 * p) = (55 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 55 p
  have h165 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (165 * p) = (165 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 165 p
  have h330 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (330 * p) = (330 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 330 p
  have h462c (j : ℕ) :
      taylorCoefficient j (462 : LaurentPolynomial ℚ) =
        (462 : ℚ) * ((0 : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ)) := by
    exact taylorCoefficient_natCast j 462
  simp only [h11, h55, h165, h330, h462c]
  norm_num [Nat.factorial]

theorem taylor_nine : (List.range 10).map (fun j => taylorCoefficient j (virtual 9)) =
    [0, 0, 0, 0, 0, 2048, 13312 / 3, 13568 / 3, 916096 / 315,
      3777808 / 2835] := by
  rw [virtual_9]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h10 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (10 * p) = (10 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 10 p
  have h44 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (44 * p) = (44 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 44 p
  have h110 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (110 * p) = (110 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 110 p
  have h165 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (165 * p) = (165 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 165 p
  have h132 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (132 * p) = (132 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 132 p
  simp only [h10, h44, h110, h165, h132]
  norm_num [Nat.factorial]

theorem taylor_ten : (List.range 11).map (fun j => taylorCoefficient j (virtual 10)) =
    [0, 0, 0, 0, 0, 0, 4096, 8192, 118784 / 15, 4661248 / 945,
      1503232 / 675] := by
  rw [virtual_10]
  norm_num [chi, Finset.sum_range_succ, List.range_succ, map_add, map_sub,
    taylorCoefficient_T, Nat.factorial]
  have h13 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (13 * p) = (13 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 13 p
  have h78 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (78 * p) = (78 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 78 p
  have h286 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (286 * p) = (286 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 286 p
  have h715 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (715 * p) = (715 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 715 p
  have h1287 (j : ℕ) (p : LaurentPolynomial ℚ) :
      taylorCoefficient j (1287 * p) = (1287 : ℚ) * taylorCoefficient j p := by
    exact taylorCoefficient_nat_mul j 1287 p
  have h1716c (j : ℕ) :
      taylorCoefficient j (1716 : LaurentPolynomial ℚ) =
        (1716 : ℚ) * ((0 : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ)) := by
    exact taylorCoefficient_natCast j 1716
  simp only [h13, h78, h286, h715, h1287, h1716c]
  norm_num [Nat.factorial]

theorem taylor_two_coeff (j : Fin 3) :
    taylorCoefficient j (virtual 2) = ([0, 0, 16] : List ℚ).get j := by
  have h := congrArg (fun l : List ℚ => l[j.val]?) taylor_two
  simpa [List.getElem?_map, List.getElem_range, j.isLt] using h

end
end QuaternionicSymmetry.Characters
