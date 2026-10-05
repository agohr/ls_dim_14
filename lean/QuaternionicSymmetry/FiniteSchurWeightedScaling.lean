import QuaternionicSymmetry.FiniteTypeCSchurSix

/-! Weighted homogeneity and curvature-sign substitution for the exact
finite Schur/orbital polynomials used by the certificates. -/

namespace QuaternionicSymmetry.FiniteSchurWeightedScaling

open FiniteTypeCSchurSix

noncomputable section

variable {S : Type*} [CommRing S] [Algebra ℚ S]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem schur_weightedScaling (c : S) (p : Fin 6 → S) (k : ℕ) (hk : k ≤ 6)
    (lam : List ℕ) (hlam : lam ∈ partitions k) :
    MvPolynomial.aeval (fun i : Fin 6 => c ^ (i.val + 1) * p i) (schur lam) =
      c ^ k * MvPolynomial.aeval p (schur lam) := by
  interval_cases k
  · norm_num [partitions] at hlam
    rcases hlam with rfl
    all_goals norm_num [schur, h0, h1, h2, h3, h4, h5, h6, e1, e2, e3, e4, e5, e6, p1, p2, p3, p4, p5, p6]
  · norm_num [partitions] at hlam
    rcases hlam with rfl
    all_goals norm_num [schur, h0, h1, h2, h3, h4, h5, h6, e1, e2, e3, e4, e5, e6, p1, p2, p3, p4, p5, p6]
  · norm_num [partitions] at hlam
    rcases hlam with rfl | rfl
    all_goals (norm_num [schur, h0, h1, h2, h3, h4, h5, h6, e1, e2, e3, e4, e5, e6, p1, p2, p3, p4, p5, p6]; ring)
  · norm_num [partitions] at hlam
    rcases hlam with rfl | rfl | rfl
    all_goals (norm_num [schur, h0, h1, h2, h3, h4, h5, h6, e1, e2, e3, e4, e5, e6, p1, p2, p3, p4, p5, p6]; ring)
  · norm_num [partitions] at hlam
    rcases hlam with rfl | rfl | rfl | rfl | rfl
    all_goals (norm_num [schur, h0, h1, h2, h3, h4, h5, h6, e1, e2, e3, e4, e5, e6, p1, p2, p3, p4, p5, p6]; ring)
  · norm_num [partitions] at hlam
    rcases hlam with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (norm_num [schur, h0, h1, h2, h3, h4, h5, h6, e1, e2, e3, e4, e5, e6, p1, p2, p3, p4, p5, p6]; ring)
  · norm_num [partitions] at hlam
    rcases hlam with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (norm_num [schur, h0, h1, h2, h3, h4, h5, h6, e1, e2, e3, e4, e5, e6, p1, p2, p3, p4, p5, p6]; ring)

theorem orbital_weightedScaling (c : S) (p : Fin 6 → S) (n k : ℕ)
    (hk : k ≤ 6) (a : List ℕ) :
    MvPolynomial.aeval (fun i : Fin 6 => c ^ (i.val + 1) * p i) (orbital n k a) =
      c ^ k * MvPolynomial.aeval p (orbital n k a) := by
  unfold orbital
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lam hlam
  rw [schur_weightedScaling c p k hk lam (List.mem_toFinset.mp hlam)]
  ring

theorem orbital_sign (p : Fin 6 → S) (n k : ℕ) (hk : k ≤ 6) (a : List ℕ) :
    MvPolynomial.aeval (fun i : Fin 6 => (-1 : S) ^ (i.val + 1) * p i)
        (orbital n k a) =
      (-1 : S) ^ k * MvPolynomial.aeval p (orbital n k a) :=
  orbital_weightedScaling (-1) p n k hk a

end
end QuaternionicSymmetry.FiniteSchurWeightedScaling
