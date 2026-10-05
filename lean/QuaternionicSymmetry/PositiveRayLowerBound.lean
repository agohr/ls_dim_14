import QuaternionicSymmetry.PositiveRay

/-! A lower bound against every positive linear functional is an actual
lower bound for the coefficient along a nonzero positive ray. -/
namespace QuaternionicSymmetry.PositiveRayLowerBound
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem exists_coefficient_ge {v x : V} (hv : v ≠ 0) (c : ℝ)
    (h : ∀ F : V →ₗ[ℝ] ℝ, 0 ≤ F v → c * F v ≤ F x) :
    ∃ r : ℝ, c ≤ r ∧ x = r • v := by
  have hr : PositiveRay.Contains v (x - c • v) := by
    apply (PositiveRay.contains_iff_functional_nonneg hv).mpr
    intro F hF
    rw [map_sub, map_smul, smul_eq_mul]
    exact sub_nonneg.mpr (h F hF)
  obtain ⟨r, hr, he⟩ := hr
  refine ⟨c+r, by linarith, ?_⟩
  have hx : x = r • v + c • v := (sub_eq_iff_eq_add).mp he
  rw [hx, add_smul, add_comm]

theorem reflect_injective {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (hf : Function.Injective f) {v x : V}
    (h : PositiveRay.Contains (f v) (f x)) : PositiveRay.Contains v x := by
  obtain ⟨r, hr, he⟩ := h
  refine ⟨r, hr, hf ?_⟩
  simpa only [map_smul] using he

end QuaternionicSymmetry.PositiveRayLowerBound
