import QuaternionicSymmetry.TorusFaithfulWeightSpan

/-! Source-free real-span transfer through the exact equation `μ = k • ν`
between complete contact-power section weights and actual fixed-twistor
vertical weights. No convex or geometric exposure claim is hidden here. -/

namespace QuaternionicSymmetry.TorusScaledWeightSpanTransfer

open TorusFaithfulWeightSpan
noncomputable section

variable {r : ℕ}

theorem integralWeightLinear_nsmul (k : ℕ) (ν : Fin r → ℤ) :
    integralWeightLinear (k • ν) = (k : ℝ) • integralWeightLinear ν := by
  apply LinearMap.ext
  intro u
  simp only [integralWeightLinear_apply, LinearMap.smul_apply,
    Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.mul_apply, Pi.natCast_apply, Int.cast_mul, Int.cast_natCast]
  ring

theorem span_top_of_scaled_realization (k : ℕ)
    (S T : Set (Fin r → ℤ))
    (hSpan : Submodule.span ℝ
      (integralWeightLinear '' S) = ⊤)
    (hRealize : ∀ μ ∈ S, ∃ ν ∈ T, k • ν = μ) :
    Submodule.span ℝ (integralWeightLinear '' T) = ⊤ := by
  let U := Submodule.span ℝ (integralWeightLinear '' T)
  have hSubset : integralWeightLinear '' S ⊆ U := by
    rintro _ ⟨μ,hμ,rfl⟩
    obtain ⟨ν,hν,hEq⟩ := hRealize μ hμ
    rw [← hEq, integralWeightLinear_nsmul]
    exact U.smul_mem (k : ℝ) (Submodule.subset_span ⟨ν,hν,rfl⟩)
  have hLe : Submodule.span ℝ (integralWeightLinear '' S) ≤ U :=
    Submodule.span_le.mpr hSubset
  rw [hSpan] at hLe
  exact top_unique hLe

end
end QuaternionicSymmetry.TorusScaledWeightSpanTransfer
