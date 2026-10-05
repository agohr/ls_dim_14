import QuaternionicSymmetry.RealToComplexTangentComplexificationLinear

/-! The image of the actual complex-linear tensor extension of a real
linear map is precisely the complex span of its real image. -/

namespace QuaternionicSymmetry.RealComplexifiedMapRange

open RealToComplexTangentComplexification
open scoped TensorProduct
noncomputable section

variable {U H : Type*} [AddCommGroup U] [Module ℝ U]
  [AddCommGroup H] [Module ℂ H]

theorem range_complexifiedMapComplex (f : U →ₗ[ℝ] H) :
    LinearMap.range (complexifiedMapComplex f) =
      Submodule.span ℂ (Set.range f) := by
  apply le_antisymm
  · rintro y ⟨t,rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul z u =>
        simp only [complexifiedMapComplex_tmul]
        exact Submodule.smul_mem _ z (Submodule.subset_span ⟨u,rfl⟩)
    | add x y hx hy =>
        simpa only [map_add] using Submodule.add_mem _ hx hy
  · apply Submodule.span_le.mpr
    rintro y ⟨u,rfl⟩
    exact ⟨(1 : ℂ) ⊗ₜ[ℝ] u, by simp⟩

theorem surjective_complexifiedMapComplex_of_span_range_top
    (f : U →ₗ[ℝ] H)
    (hSpan : Submodule.span ℂ (Set.range f) = ⊤) :
    Function.Surjective (complexifiedMapComplex f) := by
  rw [← LinearMap.range_eq_top, range_complexifiedMapComplex]
  exact hSpan

end
end QuaternionicSymmetry.RealComplexifiedMapRange
