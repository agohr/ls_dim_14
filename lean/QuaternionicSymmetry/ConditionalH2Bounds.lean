import QuaternionicSymmetry.Arithmetic

/-! Finite integer consequences of the dimension-thirteen and -fourteen
scalar reserves. The index equality, positive volume, and nonnegative
remainder are explicit hypotheses; the actual polynomial assembly is in the
H2 witness modules and their linear-functional bridge. -/

namespace QuaternionicSymmetry.ConditionalH2Bounds

theorem bound13 {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 13 : ℝ) + 392 * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 15 ≤ d := by
  have h := QuaternionicSymmetry.lower_bound_of_positive_certificate
    (n := 13) (C := 392) hindex (by norm_num) hU hR
  norm_num [QuaternionicSymmetry.delta] at h ⊢
  exact h

theorem bound14 {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 14 : ℝ) + 448 * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 18 ≤ d := by
  have h := QuaternionicSymmetry.lower_bound_of_positive_certificate
    (n := 14) (C := 448) hindex (by norm_num) hU hR
  norm_num [QuaternionicSymmetry.delta] at h ⊢
  exact h

theorem no_small_symmetry13 {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 13 : ℝ) + 392 * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) (hsmall : d ≤ 3) : False := by
  have h := bound13 hindex hU hR
  omega

theorem no_small_symmetry14 {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 14 : ℝ) + 448 * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) (hsmall : d ≤ 3) : False := by
  have h := bound14 hindex hU hR
  omega

end QuaternionicSymmetry.ConditionalH2Bounds
