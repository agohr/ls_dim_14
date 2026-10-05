import QuaternionicSymmetry.ComplexifiedLieCentralizerComponents
import QuaternionicSymmetry.RealToComplexTangentComplexificationLinear

/-! The complexified image of a real differential range is exactly the
complex span of the composed differential generators. This literal image
equality connects BG-L1's curve-velocity Lie span to the selected contact
toral Lie subalgebra; no dimension or classification input appears. -/

namespace QuaternionicSymmetry.ComplexifiedDerivativeRangeSpan

open ComplexifiedLieCentralizerComponents
open RealToComplexTangentComplexification
open scoped TensorProduct
noncomputable section

variable {W L V : Type*} [AddCommGroup W] [Module ℝ W]
  [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup V] [Module ℂ V]

theorem complexSpan_range_map_eq_span_composition
    (g : W →ₗ[ℝ] L) (f : L →ₗ[ℝ] V) :
    (complexSpan (LinearMap.range g)).map (complexifiedMapComplex f) =
      Submodule.span ℂ (Set.range (fun w : W => f (g w))) := by
  apply le_antisymm
  · rintro z ⟨t,ht,rfl⟩
    induction ht using Submodule.span_induction with
    | mem t ht =>
        obtain ⟨u,rfl⟩ := ht
        obtain ⟨w,hw⟩ := u.2
        change (complexifiedMapComplex f) ((1 : ℂ) ⊗ₜ[ℝ] (u : L)) ∈ _
        rw [← hw]
        simpa only [complexifiedMapComplex_tmul, one_smul] using
          (Submodule.subset_span (Set.mem_range_self w) :
            f (g w) ∈ Submodule.span ℂ (Set.range (fun w : W => f (g w))))
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using
        (Submodule.span ℂ (Set.range (fun w : W => f (g w)))).add_mem ihx ihy
    | smul a x hx ihx => simpa only [map_smul] using
        (Submodule.span ℂ (Set.range (fun w : W => f (g w)))).smul_mem a ihx
  · intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨w,rfl⟩ := hz
        refine ⟨(1 : ℂ) ⊗ₜ[ℝ] (g w),
          one_tmul_mem_complexSpan _ ⟨w,rfl⟩, ?_⟩
        simp only [complexifiedMapComplex_tmul, one_smul]
    | zero => simp
    | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
    | smul a x hx ihx => exact Submodule.smul_mem _ a ihx

end
end QuaternionicSymmetry.ComplexifiedDerivativeRangeSpan
