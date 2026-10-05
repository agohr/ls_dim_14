import QuaternionicSymmetry.TorusWeightHalfTurn

/-! Integral weights are separated by their actual standard-torus characters.
Tensor powers multiply the integral weight, with no source premise. -/
namespace QuaternionicSymmetry.TorusWeightSeparation

open ManifoldQuaternionicTorusAction TorusWeightHalfTurn
noncomputable section

theorem weightCharacter_sub {r : ℕ} (μ ν : Fin r → ℤ) (t : Torus r) :
    weightCharacter (μ - ν) t = weightCharacter μ t / weightCharacter ν t := by
  classical
  change (∏ i : Fin r, t i ^ (μ i - ν i)) =
    (∏ i : Fin r, t i ^ μ i) / (∏ i : Fin r, t i ^ ν i)
  simp_rw [zpow_sub]
  simpa only [div_eq_mul_inv] using
    (Finset.prod_div_distrib (s := Finset.univ)
      (fun i : Fin r => t i ^ μ i) (fun i : Fin r => t i ^ ν i))

theorem weightCharacter_nsmul {r : ℕ} (k : ℕ) (μ : Fin r → ℤ) (t : Torus r) :
    weightCharacter (k • μ) t = weightCharacter μ t ^ k := by
  classical
  change (∏ i : Fin r, t i ^ (k • μ) i) = (∏ i : Fin r, t i ^ μ i) ^ k
  simp only [Pi.smul_apply, nsmul_eq_mul]
  simp_rw [mul_comm (k : ℤ), zpow_mul, zpow_natCast]
  exact Finset.prod_pow _ _ _

theorem weightCharacter_injective {r : ℕ} :
    Function.Injective (fun μ : Fin r → ℤ => weightCharacter μ) := by
  intro μ ν h
  by_contra hne
  obtain ⟨t,ht⟩ := exists_halfTurn (μ - ν) (sub_ne_zero.mpr hne)
  have hc : weightCharacter μ t = weightCharacter ν t := congrArg (fun χ => χ t) h
  rw [weightCharacter_sub, hc] at ht
  simp only [div_self', Circle.coe_one] at ht
  norm_num at ht

theorem weight_eq_of_character_eq {r : ℕ} {μ ν : Fin r → ℤ}
    (h : ∀ t : Torus r, weightCharacter μ t = weightCharacter ν t) : μ = ν :=
  weightCharacter_injective (MonoidHom.ext h)

end
end QuaternionicSymmetry.TorusWeightSeparation
