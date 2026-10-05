import QuaternionicSymmetry.TorusIntegralGenericCocharacter

/-! Every integral support direction of a finite nonempty integral weight
family has a minimum which is also exposed by a separating integral
cocharacter. The original minimum value is retained, including when its
face contains several different weights. -/
namespace QuaternionicSymmetry.TorusIntegralExposedRefinement

open TorusIntegralCocharacter TorusIntegralGenericCocharacter
open scoped BigOperators
noncomputable section

private theorem pairing_perturb {r : ℕ} (μ u v : Fin r → ℤ) (N : ℤ) :
    pairing μ (N • u + v) = N * pairing μ u + pairing μ v := by
  simp only [pairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem exists_exposed_minimum_refining {r : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (μ : ι → Fin r → ℤ) (u : Fin r → ℤ) :
    ∃ (j : ι) (w : Fin r → ℤ),
      (∀ i, pairing (μ j) u ≤ pairing (μ i) u) ∧
      (∀ i, pairing (μ j) w ≤ pairing (μ i) w) ∧
      ∀ i, pairing (μ i) w = pairing (μ j) w → μ i = μ j := by
  classical
  obtain ⟨v,hv⟩ := exists_separating_cocharacter μ
  obtain ⟨ij,_,hij⟩ := Finset.exists_max_image Finset.univ
    (fun p : ι × ι => pairing (μ p.1) v - pairing (μ p.2) v)
    Finset.univ_nonempty
  let N := pairing (μ ij.1) v - pairing (μ ij.2) v + 1
  have hN (i j : ι) : pairing (μ i) v - pairing (μ j) v < N := by
    have h := hij (i,j) (Finset.mem_univ _)
    dsimp only at h
    dsimp [N]
    omega
  have hNpos : 0 < N := by simpa using hN ij.1 ij.1
  let w : Fin r → ℤ := N • u + v
  have hform (i : ι) : pairing (μ i) w =
      N * pairing (μ i) u + pairing (μ i) v := pairing_perturb _ _ _ _
  have hlt (i j : ι) (h : pairing (μ i) u < pairing (μ j) u) :
      pairing (μ i) w < pairing (μ j) w := by
    have hgap : pairing (μ i) u + 1 ≤ pairing (μ j) u := h
    have hb := hN i j
    rw [hform i,hform j]
    nlinarith
  have hw (i j : ι) (h : pairing (μ i) w = pairing (μ j) w) : μ i = μ j := by
    have he : pairing (μ i) u = pairing (μ j) u := by
      rcases lt_trichotomy (pairing (μ i) u) (pairing (μ j) u) with hi | he | hi
      · exact False.elim ((ne_of_lt (hlt i j hi)) h)
      · exact he
      · exact False.elim ((ne_of_lt (hlt j i hi)) h.symm)
    apply hv i j
    rw [hform i,hform j,he] at h
    exact add_left_cancel h
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ
    (fun i => pairing (μ i) w) Finset.univ_nonempty
  refine ⟨j,w,?_,fun i => hj i (Finset.mem_univ i),fun i hi => hw i j hi⟩
  intro i
  by_contra hi
  have h := hlt i j (lt_of_not_ge hi)
  exact (not_lt_of_ge (hj i (Finset.mem_univ i))) h

theorem exists_nonzero_exposed_minimum {r : ℕ} {ι : Type*}
    [Fintype ι] (μ : ι → Fin r → ℤ) (hμ : ∃ i, μ i ≠ 0) :
    ∃ (j : ι) (w : Fin r → ℤ), μ j ≠ 0 ∧
      (∀ i, pairing (μ j) w ≤ pairing (μ i) w) ∧
      ∀ i, pairing (μ i) w = pairing (μ j) w → μ i = μ j := by
  classical
  obtain ⟨i,hi⟩ := hμ
  letI : Nonempty ι := ⟨i⟩
  have hk : ∃ k : Fin r, μ i k ≠ 0 := by
    by_contra! h
    exact hi (funext h)
  obtain ⟨k,hk⟩ := hk
  have hu : ∃ u : Fin r → ℤ, pairing (μ i) u < 0 := by
    rcases lt_or_gt_of_ne hk with hneg | hpos
    · refine ⟨Pi.single k 1, ?_⟩
      simpa [pairing, Pi.single_apply, mul_ite] using hneg
    · refine ⟨Pi.single k (-1), ?_⟩
      simpa [pairing, Pi.single_apply, mul_ite] using neg_neg_of_pos hpos
  obtain ⟨u,hu⟩ := hu
  obtain ⟨j,w,hMin,hMin',hFace⟩ := exists_exposed_minimum_refining μ u
  refine ⟨j,w,?_,hMin',hFace⟩
  intro hz
  have hj := (hMin i).trans_lt hu
  simpa [hz,pairing] using hj

end
end QuaternionicSymmetry.TorusIntegralExposedRefinement
