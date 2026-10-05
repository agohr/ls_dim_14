import QuaternionicSymmetry.HigherCharacters
import QuaternionicSymmetry.Arithmetic

/-!
The finite, additive part of the virtual-index argument.  An index functional
on the character group, valued in any commutative rational algebra, is kept explicit: constructing it from a twistor space
and proving its characteristic-class interpretation are separate geometric
tasks.  The hypotheses below are precisely the special Hilbert values used
by the textbook, after identifying `chi (n+2r)` with the twist at `r`.
-/

namespace QuaternionicSymmetry.IndexCharacterDeduction

open LaurentPolynomial Characters

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

def SpecialValues (n : ℕ) (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R) : Prop :=
  index (chi (n + 2)) = d ∧ index (chi n) = 1 ∧
    ∀ q : ℕ, q < n → q % 2 = n % 2 → index (chi q) = 0

/-- The cohomological Hilbert values, with twist comparison restricted to
nonnegative symmetric powers `n+2r`. Negative Hilbert arguments are supplied
by the twistor Euler characteristic, not by a negative symmetric power. -/
def HilbertValues (n : ℕ) (d : R) (P : ℤ → R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R) : Prop :=
  P 0 = 1 ∧ P 1 = d ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ n → P (-(j : ℤ)) = 0) ∧
    (∀ r : ℤ, 0 ≤ (n : ℤ) + 2 * r →
      index (chi (((n : ℤ) + 2 * r).toNat)) = P r)

theorem specialValues_of_hilbert {n : ℕ} {d : R} {P : ℤ → R}
    {index : LaurentPolynomial ℚ →ₗ[ℚ] R}
    (h : HilbertValues n d P index) : SpecialValues n d index := by
  rcases h with ⟨hzero, hone, hnegative, htwist⟩
  refine ⟨?_, ?_, ?_⟩
  · have ht := htwist 1 (by omega)
    simpa using ht.trans hone
  · have ht := htwist 0 (by omega)
    simpa using ht.trans hzero
  · intro q hq hparity
    let j := (n - q) / 2
    have hj : 1 ≤ j := by dsimp [j]; omega
    have hjn : j ≤ n := by dsimp [j]; omega
    have heq : (n : ℤ) + 2 * (-(j : ℤ)) = (q : ℤ) := by
      dsimp [j]
      omega
    have ht := htwist (-(j : ℤ)) (by omega)
    rw [heq, Int.toNat_natCast] at ht
    exact ht.trans (hnegative j hj hjn)

/-- Additivity and the special Hilbert values give the virtual index in dimension 2. -/
theorem virtual_index_2 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 2 d index) : index (virtual 2) = d - (delta 2 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [Characters.virtual_two]
  simp only [map_add, map_sub]
  rw [
    show index (5 * chi 2) = (5 : R) * index (chi 2) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 5 (chi 2)),
    show index (10 * chi 0) = (10 : R) * index (chi 0) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 10 (chi 0))]
  rw [hlow 0 (by omega) (by decide)]
  rw [show 2 + 2 = 4 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 3. -/
theorem virtual_index_3 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 3 d index) : index (virtual 3) = d - (delta 3 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [Characters.virtual_3]
  simp only [map_add, map_sub]
  rw [
    show index (4 * chi 3) = (4 : R) * index (chi 3) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 4 (chi 3)),
    show index (5 * chi 1) = (5 : R) * index (chi 1) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 5 (chi 1))]
  rw [hlow 1 (by omega) (by decide)]
  rw [show 3 + 2 = 5 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 4. -/
theorem virtual_index_4 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 4 d index) : index (virtual 4) = d - (delta 4 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [Characters.virtual_4]
  simp only [map_add, map_sub]
  rw [
    show index (7 * chi 4) = (7 : R) * index (chi 4) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 7 (chi 4)),
    show index (21 * chi 2) = (21 : R) * index (chi 2) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 21 (chi 2)),
    show index (35 * chi 0) = (35 : R) * index (chi 0) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 35 (chi 0))]
  rw [hlow 2 (by omega) (by decide), hlow 0 (by omega) (by decide)]
  rw [show 4 + 2 = 6 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 5. -/
theorem virtual_index_5 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 5 d index) : index (virtual 5) = d - (delta 5 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [Characters.virtual_5]
  simp only [map_add, map_sub]
  rw [
    show index (6 * chi 5) = (6 : R) * index (chi 5) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 6 (chi 5)),
    show index (14 * chi 3) = (14 : R) * index (chi 3) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 14 (chi 3)),
    show index (14 * chi 1) = (14 : R) * index (chi 1) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 14 (chi 1))]
  rw [hlow 3 (by omega) (by decide), hlow 1 (by omega) (by decide)]
  rw [show 5 + 2 = 7 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 6. -/
theorem virtual_index_6 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 6 d index) : index (virtual 6) = d - (delta 6 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [Characters.virtual_6]
  simp only [map_add, map_sub]
  rw [
    show index (9 * chi 6) = (9 : R) * index (chi 6) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 9 (chi 6)),
    show index (36 * chi 4) = (36 : R) * index (chi 4) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 36 (chi 4)),
    show index (84 * chi 2) = (84 : R) * index (chi 2) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 84 (chi 2)),
    show index (126 * chi 0) = (126 : R) * index (chi 0) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 126 (chi 0))]
  rw [hlow 4 (by omega) (by decide), hlow 2 (by omega) (by decide), hlow 0 (by omega) (by decide)]
  rw [show 6 + 2 = 8 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 7. -/
theorem virtual_index_7 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 7 d index) : index (virtual 7) = d - (delta 7 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [Characters.virtual_7]
  simp only [map_add, map_sub]
  rw [
    show index (8 * chi 7) = (8 : R) * index (chi 7) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 8 (chi 7)),
    show index (27 * chi 5) = (27 : R) * index (chi 5) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 27 (chi 5)),
    show index (48 * chi 3) = (48 : R) * index (chi 3) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 48 (chi 3)),
    show index (42 * chi 1) = (42 : R) * index (chi 1) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 42 (chi 1))]
  rw [hlow 5 (by omega) (by decide), hlow 3 (by omega) (by decide), hlow 1 (by omega) (by decide)]
  rw [show 7 + 2 = 9 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 8. -/
theorem virtual_index_8 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 8 d index) : index (virtual 8) = d - (delta 8 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [Characters.virtual_8]
  simp only [map_add, map_sub]
  rw [
    show index (11 * chi 8) = (11 : R) * index (chi 8) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 11 (chi 8)),
    show index (55 * chi 6) = (55 : R) * index (chi 6) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 55 (chi 6)),
    show index (165 * chi 4) = (165 : R) * index (chi 4) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 165 (chi 4)),
    show index (330 * chi 2) = (330 : R) * index (chi 2) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 330 (chi 2)),
    show index (462 * chi 0) = (462 : R) * index (chi 0) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 462 (chi 0))]
  rw [hlow 6 (by omega) (by decide), hlow 4 (by omega) (by decide), hlow 2 (by omega) (by decide), hlow 0 (by omega) (by decide)]
  rw [show 8 + 2 = 10 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 9. -/
theorem virtual_index_9 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 9 d index) : index (virtual 9) = d - (delta 9 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [Characters.virtual_9]
  simp only [map_add, map_sub]
  rw [
    show index (10 * chi 9) = (10 : R) * index (chi 9) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 10 (chi 9)),
    show index (44 * chi 7) = (44 : R) * index (chi 7) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 44 (chi 7)),
    show index (110 * chi 5) = (110 : R) * index (chi 5) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 110 (chi 5)),
    show index (165 * chi 3) = (165 : R) * index (chi 3) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 165 (chi 3)),
    show index (132 * chi 1) = (132 : R) * index (chi 1) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 132 (chi 1))]
  rw [hlow 7 (by omega) (by decide), hlow 5 (by omega) (by decide), hlow 3 (by omega) (by decide), hlow 1 (by omega) (by decide)]
  rw [show 9 + 2 = 11 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 10. -/
theorem virtual_index_10 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 10 d index) : index (virtual 10) = d - (delta 10 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [Characters.virtual_10]
  simp only [map_add, map_sub]
  rw [
    show index (13 * chi 10) = (13 : R) * index (chi 10) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 13 (chi 10)),
    show index (78 * chi 8) = (78 : R) * index (chi 8) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 78 (chi 8)),
    show index (286 * chi 6) = (286 : R) * index (chi 6) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 286 (chi 6)),
    show index (715 * chi 4) = (715 : R) * index (chi 4) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 715 (chi 4)),
    show index (1287 * chi 2) = (1287 : R) * index (chi 2) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 1287 (chi 2)),
    show index (1716 * chi 0) = (1716 : R) * index (chi 0) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 1716 (chi 0))]
  rw [hlow 8 (by omega) (by decide), hlow 6 (by omega) (by decide), hlow 4 (by omega) (by decide), hlow 2 (by omega) (by decide), hlow 0 (by omega) (by decide)]
  rw [show 10 + 2 = 12 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 11. -/
theorem virtual_index_11 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 11 d index) : index (virtual 11) = d - (delta 11 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [HigherCharacters.virtual_eleven]
  simp only [map_add, map_sub]
  rw [
    show index (12 * chi 11) = (12 : R) * index (chi 11) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 12 (chi 11)),
    show index (65 * chi 9) = (65 : R) * index (chi 9) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 65 (chi 9)),
    show index (208 * chi 7) = (208 : R) * index (chi 7) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 208 (chi 7)),
    show index (429 * chi 5) = (429 : R) * index (chi 5) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 429 (chi 5)),
    show index (572 * chi 3) = (572 : R) * index (chi 3) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 572 (chi 3)),
    show index (429 * chi 1) = (429 : R) * index (chi 1) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 429 (chi 1))]
  rw [hlow 9 (by omega) (by decide), hlow 7 (by omega) (by decide), hlow 5 (by omega) (by decide), hlow 3 (by omega) (by decide), hlow 1 (by omega) (by decide)]
  rw [show 11 + 2 = 13 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 12. -/
theorem virtual_index_12 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 12 d index) : index (virtual 12) = d - (delta 12 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [HigherCharacters.virtual_twelve]
  simp only [map_add, map_sub]
  rw [
    show index (15 * chi 12) = (15 : R) * index (chi 12) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 15 (chi 12)),
    show index (105 * chi 10) = (105 : R) * index (chi 10) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 105 (chi 10)),
    show index (455 * chi 8) = (455 : R) * index (chi 8) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 455 (chi 8)),
    show index (1365 * chi 6) = (1365 : R) * index (chi 6) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 1365 (chi 6)),
    show index (3003 * chi 4) = (3003 : R) * index (chi 4) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 3003 (chi 4)),
    show index (5005 * chi 2) = (5005 : R) * index (chi 2) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 5005 (chi 2)),
    show index (6435 * chi 0) = (6435 : R) * index (chi 0) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 6435 (chi 0))]
  rw [hlow 10 (by omega) (by decide), hlow 8 (by omega) (by decide), hlow 6 (by omega) (by decide), hlow 4 (by omega) (by decide), hlow 2 (by omega) (by decide), hlow 0 (by omega) (by decide)]
  rw [show 12 + 2 = 14 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 13. -/
theorem virtual_index_13 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 13 d index) : index (virtual 13) = d - (delta 13 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [HigherCharacters.virtual_thirteen]
  simp only [map_add, map_sub]
  rw [
    show index (14 * chi 13) = (14 : R) * index (chi 13) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 14 (chi 13)),
    show index (90 * chi 11) = (90 : R) * index (chi 11) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 90 (chi 11)),
    show index (350 * chi 9) = (350 : R) * index (chi 9) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 350 (chi 9)),
    show index (910 * chi 7) = (910 : R) * index (chi 7) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 910 (chi 7)),
    show index (1638 * chi 5) = (1638 : R) * index (chi 5) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 1638 (chi 5)),
    show index (2002 * chi 3) = (2002 : R) * index (chi 3) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 2002 (chi 3)),
    show index (1430 * chi 1) = (1430 : R) * index (chi 1) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 1430 (chi 1))]
  rw [hlow 11 (by omega) (by decide), hlow 9 (by omega) (by decide), hlow 7 (by omega) (by decide), hlow 5 (by omega) (by decide), hlow 3 (by omega) (by decide), hlow 1 (by omega) (by decide)]
  rw [show 13 + 2 = 15 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- Additivity and the special Hilbert values give the virtual index in dimension 14. -/
theorem virtual_index_14 (d : R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : SpecialValues 14 d index) : index (virtual 14) = d - (delta 14 : R) := by
  rcases h with ⟨hhigh, hmid, hlow⟩
  rw [HigherCharacters.virtual_fourteen]
  simp only [map_add, map_sub]
  rw [
    show index (17 * chi 14) = (17 : R) * index (chi 14) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 17 (chi 14)),
    show index (136 * chi 12) = (136 : R) * index (chi 12) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 136 (chi 12)),
    show index (680 * chi 10) = (680 : R) * index (chi 10) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 680 (chi 10)),
    show index (2380 * chi 8) = (2380 : R) * index (chi 8) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 2380 (chi 8)),
    show index (6188 * chi 6) = (6188 : R) * index (chi 6) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 6188 (chi 6)),
    show index (12376 * chi 4) = (12376 : R) * index (chi 4) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 12376 (chi 4)),
    show index (19448 * chi 2) = (19448 : R) * index (chi 2) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 19448 (chi 2)),
    show index (24310 * chi 0) = (24310 : R) * index (chi 0) by
      simpa only [nsmul_eq_mul] using (map_nsmul index.toAddMonoidHom 24310 (chi 0))]
  rw [hlow 12 (by omega) (by decide), hlow 10 (by omega) (by decide), hlow 8 (by omega) (by decide), hlow 6 (by omega) (by decide), hlow 4 (by omega) (by decide), hlow 2 (by omega) (by decide), hlow 0 (by omega) (by decide)]
  rw [show 14 + 2 = 16 by omega] at hhigh
  rw [hhigh, hmid]
  norm_num [delta]

/-- The checked character range. The only Hilbert/twist premises are those in
`HilbertValues`; all character decompositions are the existing ring proofs. -/
theorem virtual_index_of_hilbert {n : ℕ} (hnlow : 2 ≤ n) (hnhigh : n ≤ 14)
    (d : R) (P : ℤ → R)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] R)
    (h : HilbertValues n d P index) :
    index (virtual n) = d - (delta n : R) := by
  have hs := specialValues_of_hilbert h
  interval_cases n <;>
    first
    | exact virtual_index_2 d index hs
    | exact virtual_index_3 d index hs
    | exact virtual_index_4 d index hs
    | exact virtual_index_5 d index hs
    | exact virtual_index_6 d index hs
    | exact virtual_index_7 d index hs
    | exact virtual_index_8 d index hs
    | exact virtual_index_9 d index hs
    | exact virtual_index_10 d index hs
    | exact virtual_index_11 d index hs
    | exact virtual_index_12 d index hs
    | exact virtual_index_13 d index hs
    | exact virtual_index_14 d index hs

end
end QuaternionicSymmetry.IndexCharacterDeduction
