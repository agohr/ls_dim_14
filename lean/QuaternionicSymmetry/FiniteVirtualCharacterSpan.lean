import QuaternionicSymmetry.IndexCharacterDeduction

/-! Finite linear extension from descended symmetric-power characters to the
virtual character. Only the parity-compatible nonnegative twists occur. -/
namespace QuaternionicSymmetry.FiniteVirtualCharacterSpan
open Characters LaurentPolynomial
noncomputable section

variable {R : Type} [CommRing R] [Algebra ℚ R]

private theorem map_nat_mul (f : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (m : ℕ) (p : LaurentPolynomial ℚ) :
    f ((m : LaurentPolynomial ℚ) * p) = (m : R) * f p := by
  simpa only [nsmul_eq_mul] using map_nsmul f.toAddMonoidHom m p

private theorem map_nat_mul_eq_of_chi
    (f g : LaurentPolynomial ℚ →ₗ[ℚ] R) (m q : ℕ)
    (h : f (chi q) = g (chi q)) :
    f ((m : LaurentPolynomial ℚ) * chi q) =
      g ((m : LaurentPolynomial ℚ) * chi q) := by
  rw [map_nat_mul f, map_nat_mul g, h]

theorem maps_virtual_eq_of_chi
    (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14)
    (f g : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (hchi : ∀ q : ℕ, q ≤ n+2 → q % 2 = n % 2 → f (chi q) = g (chi q)) :
    f (virtual n) = g (virtual n) := by
  rcases hn with ⟨hn2, hn14⟩
  interval_cases n
  · rw [Characters.virtual_two]
    simp only [map_add, map_sub]
    have h5_2 : f (5 * chi 2) = g (5 * chi 2) := by
      simpa using map_nat_mul_eq_of_chi f g 5 2 (hchi 2 (by omega) (by decide))
    have h10_0 : f (10 * chi 0) = g (10 * chi 0) := by
      simpa using map_nat_mul_eq_of_chi f g 10 0 (hchi 0 (by omega) (by decide))
    rw [hchi 4 (by omega) (by decide), h5_2, h10_0]
  · rw [Characters.virtual_3]
    simp only [map_add, map_sub]
    have h4_3 : f (4 * chi 3) = g (4 * chi 3) := by
      simpa using map_nat_mul_eq_of_chi f g 4 3 (hchi 3 (by omega) (by decide))
    have h5_1 : f (5 * chi 1) = g (5 * chi 1) := by
      simpa using map_nat_mul_eq_of_chi f g 5 1 (hchi 1 (by omega) (by decide))
    rw [hchi 5 (by omega) (by decide), h4_3, h5_1]
  · rw [Characters.virtual_4]
    simp only [map_add, map_sub]
    have h7_4 : f (7 * chi 4) = g (7 * chi 4) := by
      simpa using map_nat_mul_eq_of_chi f g 7 4 (hchi 4 (by omega) (by decide))
    have h21_2 : f (21 * chi 2) = g (21 * chi 2) := by
      simpa using map_nat_mul_eq_of_chi f g 21 2 (hchi 2 (by omega) (by decide))
    have h35_0 : f (35 * chi 0) = g (35 * chi 0) := by
      simpa using map_nat_mul_eq_of_chi f g 35 0 (hchi 0 (by omega) (by decide))
    rw [hchi 6 (by omega) (by decide), h7_4, h21_2, h35_0]
  · rw [Characters.virtual_5]
    simp only [map_add, map_sub]
    have h6_5 : f (6 * chi 5) = g (6 * chi 5) := by
      simpa using map_nat_mul_eq_of_chi f g 6 5 (hchi 5 (by omega) (by decide))
    have h14_3 : f (14 * chi 3) = g (14 * chi 3) := by
      simpa using map_nat_mul_eq_of_chi f g 14 3 (hchi 3 (by omega) (by decide))
    have h14_1 : f (14 * chi 1) = g (14 * chi 1) := by
      simpa using map_nat_mul_eq_of_chi f g 14 1 (hchi 1 (by omega) (by decide))
    rw [hchi 7 (by omega) (by decide), h6_5, h14_3, h14_1]
  · rw [Characters.virtual_6]
    simp only [map_add, map_sub]
    have h9_6 : f (9 * chi 6) = g (9 * chi 6) := by
      simpa using map_nat_mul_eq_of_chi f g 9 6 (hchi 6 (by omega) (by decide))
    have h36_4 : f (36 * chi 4) = g (36 * chi 4) := by
      simpa using map_nat_mul_eq_of_chi f g 36 4 (hchi 4 (by omega) (by decide))
    have h84_2 : f (84 * chi 2) = g (84 * chi 2) := by
      simpa using map_nat_mul_eq_of_chi f g 84 2 (hchi 2 (by omega) (by decide))
    have h126_0 : f (126 * chi 0) = g (126 * chi 0) := by
      simpa using map_nat_mul_eq_of_chi f g 126 0 (hchi 0 (by omega) (by decide))
    rw [hchi 8 (by omega) (by decide), h9_6, h36_4, h84_2, h126_0]
  · rw [Characters.virtual_7]
    simp only [map_add, map_sub]
    have h8_7 : f (8 * chi 7) = g (8 * chi 7) := by
      simpa using map_nat_mul_eq_of_chi f g 8 7 (hchi 7 (by omega) (by decide))
    have h27_5 : f (27 * chi 5) = g (27 * chi 5) := by
      simpa using map_nat_mul_eq_of_chi f g 27 5 (hchi 5 (by omega) (by decide))
    have h48_3 : f (48 * chi 3) = g (48 * chi 3) := by
      simpa using map_nat_mul_eq_of_chi f g 48 3 (hchi 3 (by omega) (by decide))
    have h42_1 : f (42 * chi 1) = g (42 * chi 1) := by
      simpa using map_nat_mul_eq_of_chi f g 42 1 (hchi 1 (by omega) (by decide))
    rw [hchi 9 (by omega) (by decide), h8_7, h27_5, h48_3, h42_1]
  · rw [Characters.virtual_8]
    simp only [map_add, map_sub]
    have h11_8 : f (11 * chi 8) = g (11 * chi 8) := by
      simpa using map_nat_mul_eq_of_chi f g 11 8 (hchi 8 (by omega) (by decide))
    have h55_6 : f (55 * chi 6) = g (55 * chi 6) := by
      simpa using map_nat_mul_eq_of_chi f g 55 6 (hchi 6 (by omega) (by decide))
    have h165_4 : f (165 * chi 4) = g (165 * chi 4) := by
      simpa using map_nat_mul_eq_of_chi f g 165 4 (hchi 4 (by omega) (by decide))
    have h330_2 : f (330 * chi 2) = g (330 * chi 2) := by
      simpa using map_nat_mul_eq_of_chi f g 330 2 (hchi 2 (by omega) (by decide))
    have h462_0 : f (462 * chi 0) = g (462 * chi 0) := by
      simpa using map_nat_mul_eq_of_chi f g 462 0 (hchi 0 (by omega) (by decide))
    rw [hchi 10 (by omega) (by decide), h11_8, h55_6, h165_4, h330_2, h462_0]
  · rw [Characters.virtual_9]
    simp only [map_add, map_sub]
    have h10_9 : f (10 * chi 9) = g (10 * chi 9) := by
      simpa using map_nat_mul_eq_of_chi f g 10 9 (hchi 9 (by omega) (by decide))
    have h44_7 : f (44 * chi 7) = g (44 * chi 7) := by
      simpa using map_nat_mul_eq_of_chi f g 44 7 (hchi 7 (by omega) (by decide))
    have h110_5 : f (110 * chi 5) = g (110 * chi 5) := by
      simpa using map_nat_mul_eq_of_chi f g 110 5 (hchi 5 (by omega) (by decide))
    have h165_3 : f (165 * chi 3) = g (165 * chi 3) := by
      simpa using map_nat_mul_eq_of_chi f g 165 3 (hchi 3 (by omega) (by decide))
    have h132_1 : f (132 * chi 1) = g (132 * chi 1) := by
      simpa using map_nat_mul_eq_of_chi f g 132 1 (hchi 1 (by omega) (by decide))
    rw [hchi 11 (by omega) (by decide), h10_9, h44_7, h110_5, h165_3, h132_1]
  · rw [Characters.virtual_10]
    simp only [map_add, map_sub]
    have h13_10 : f (13 * chi 10) = g (13 * chi 10) := by
      simpa using map_nat_mul_eq_of_chi f g 13 10 (hchi 10 (by omega) (by decide))
    have h78_8 : f (78 * chi 8) = g (78 * chi 8) := by
      simpa using map_nat_mul_eq_of_chi f g 78 8 (hchi 8 (by omega) (by decide))
    have h286_6 : f (286 * chi 6) = g (286 * chi 6) := by
      simpa using map_nat_mul_eq_of_chi f g 286 6 (hchi 6 (by omega) (by decide))
    have h715_4 : f (715 * chi 4) = g (715 * chi 4) := by
      simpa using map_nat_mul_eq_of_chi f g 715 4 (hchi 4 (by omega) (by decide))
    have h1287_2 : f (1287 * chi 2) = g (1287 * chi 2) := by
      simpa using map_nat_mul_eq_of_chi f g 1287 2 (hchi 2 (by omega) (by decide))
    have h1716_0 : f (1716 * chi 0) = g (1716 * chi 0) := by
      simpa using map_nat_mul_eq_of_chi f g 1716 0 (hchi 0 (by omega) (by decide))
    rw [hchi 12 (by omega) (by decide), h13_10, h78_8, h286_6, h715_4, h1287_2, h1716_0]
  · rw [HigherCharacters.virtual_eleven]
    simp only [map_add, map_sub]
    have h12_11 : f (12 * chi 11) = g (12 * chi 11) := by
      simpa using map_nat_mul_eq_of_chi f g 12 11 (hchi 11 (by omega) (by decide))
    have h65_9 : f (65 * chi 9) = g (65 * chi 9) := by
      simpa using map_nat_mul_eq_of_chi f g 65 9 (hchi 9 (by omega) (by decide))
    have h208_7 : f (208 * chi 7) = g (208 * chi 7) := by
      simpa using map_nat_mul_eq_of_chi f g 208 7 (hchi 7 (by omega) (by decide))
    have h429_5 : f (429 * chi 5) = g (429 * chi 5) := by
      simpa using map_nat_mul_eq_of_chi f g 429 5 (hchi 5 (by omega) (by decide))
    have h572_3 : f (572 * chi 3) = g (572 * chi 3) := by
      simpa using map_nat_mul_eq_of_chi f g 572 3 (hchi 3 (by omega) (by decide))
    have h429_1 : f (429 * chi 1) = g (429 * chi 1) := by
      simpa using map_nat_mul_eq_of_chi f g 429 1 (hchi 1 (by omega) (by decide))
    rw [hchi 13 (by omega) (by decide), h12_11, h65_9, h208_7, h429_5, h572_3, h429_1]
  · rw [HigherCharacters.virtual_twelve]
    simp only [map_add, map_sub]
    have h15_12 : f (15 * chi 12) = g (15 * chi 12) := by
      simpa using map_nat_mul_eq_of_chi f g 15 12 (hchi 12 (by omega) (by decide))
    have h105_10 : f (105 * chi 10) = g (105 * chi 10) := by
      simpa using map_nat_mul_eq_of_chi f g 105 10 (hchi 10 (by omega) (by decide))
    have h455_8 : f (455 * chi 8) = g (455 * chi 8) := by
      simpa using map_nat_mul_eq_of_chi f g 455 8 (hchi 8 (by omega) (by decide))
    have h1365_6 : f (1365 * chi 6) = g (1365 * chi 6) := by
      simpa using map_nat_mul_eq_of_chi f g 1365 6 (hchi 6 (by omega) (by decide))
    have h3003_4 : f (3003 * chi 4) = g (3003 * chi 4) := by
      simpa using map_nat_mul_eq_of_chi f g 3003 4 (hchi 4 (by omega) (by decide))
    have h5005_2 : f (5005 * chi 2) = g (5005 * chi 2) := by
      simpa using map_nat_mul_eq_of_chi f g 5005 2 (hchi 2 (by omega) (by decide))
    have h6435_0 : f (6435 * chi 0) = g (6435 * chi 0) := by
      simpa using map_nat_mul_eq_of_chi f g 6435 0 (hchi 0 (by omega) (by decide))
    rw [hchi 14 (by omega) (by decide), h15_12, h105_10, h455_8, h1365_6, h3003_4, h5005_2, h6435_0]
  · rw [HigherCharacters.virtual_thirteen]
    simp only [map_add, map_sub]
    have h14_13 : f (14 * chi 13) = g (14 * chi 13) := by
      simpa using map_nat_mul_eq_of_chi f g 14 13 (hchi 13 (by omega) (by decide))
    have h90_11 : f (90 * chi 11) = g (90 * chi 11) := by
      simpa using map_nat_mul_eq_of_chi f g 90 11 (hchi 11 (by omega) (by decide))
    have h350_9 : f (350 * chi 9) = g (350 * chi 9) := by
      simpa using map_nat_mul_eq_of_chi f g 350 9 (hchi 9 (by omega) (by decide))
    have h910_7 : f (910 * chi 7) = g (910 * chi 7) := by
      simpa using map_nat_mul_eq_of_chi f g 910 7 (hchi 7 (by omega) (by decide))
    have h1638_5 : f (1638 * chi 5) = g (1638 * chi 5) := by
      simpa using map_nat_mul_eq_of_chi f g 1638 5 (hchi 5 (by omega) (by decide))
    have h2002_3 : f (2002 * chi 3) = g (2002 * chi 3) := by
      simpa using map_nat_mul_eq_of_chi f g 2002 3 (hchi 3 (by omega) (by decide))
    have h1430_1 : f (1430 * chi 1) = g (1430 * chi 1) := by
      simpa using map_nat_mul_eq_of_chi f g 1430 1 (hchi 1 (by omega) (by decide))
    rw [hchi 15 (by omega) (by decide), h14_13, h90_11, h350_9, h910_7, h1638_5, h2002_3, h1430_1]
  · rw [HigherCharacters.virtual_fourteen]
    simp only [map_add, map_sub]
    have h17_14 : f (17 * chi 14) = g (17 * chi 14) := by
      simpa using map_nat_mul_eq_of_chi f g 17 14 (hchi 14 (by omega) (by decide))
    have h136_12 : f (136 * chi 12) = g (136 * chi 12) := by
      simpa using map_nat_mul_eq_of_chi f g 136 12 (hchi 12 (by omega) (by decide))
    have h680_10 : f (680 * chi 10) = g (680 * chi 10) := by
      simpa using map_nat_mul_eq_of_chi f g 680 10 (hchi 10 (by omega) (by decide))
    have h2380_8 : f (2380 * chi 8) = g (2380 * chi 8) := by
      simpa using map_nat_mul_eq_of_chi f g 2380 8 (hchi 8 (by omega) (by decide))
    have h6188_6 : f (6188 * chi 6) = g (6188 * chi 6) := by
      simpa using map_nat_mul_eq_of_chi f g 6188 6 (hchi 6 (by omega) (by decide))
    have h12376_4 : f (12376 * chi 4) = g (12376 * chi 4) := by
      simpa using map_nat_mul_eq_of_chi f g 12376 4 (hchi 4 (by omega) (by decide))
    have h19448_2 : f (19448 * chi 2) = g (19448 * chi 2) := by
      simpa using map_nat_mul_eq_of_chi f g 19448 2 (hchi 2 (by omega) (by decide))
    have h24310_0 : f (24310 * chi 0) = g (24310 * chi 0) := by
      simpa using map_nat_mul_eq_of_chi f g 24310 0 (hchi 0 (by omega) (by decide))
    rw [hchi 16 (by omega) (by decide), h17_14, h136_12, h680_10, h2380_8, h6188_6, h12376_4, h19448_2, h24310_0]

end
end QuaternionicSymmetry.FiniteVirtualCharacterSpan
