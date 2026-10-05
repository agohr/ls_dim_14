import QuaternionicSymmetry.RealToComplexTangentComplexification

/-! The actual complex-linear structure of the real tangent-map extension.
This strengthens, rather than changes, the previously checked real-linear
construction. -/

namespace QuaternionicSymmetry.RealToComplexTangentComplexification

open scoped TensorProduct
noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℂ W]

theorem complexifiedMap_map_complex_smul (f : V →ₗ[ℝ] W)
    (z : ℂ) (t : ℂ ⊗[ℝ] V) :
    complexifiedMap f (z • t) = z • complexifiedMap f t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
      simp only [TensorProduct.smul_tmul', complexifiedMap_tmul, smul_assoc]
  | add x y hx hy => simp [smul_add, map_add, hx, hy]

/-- The genuine complex-linear extension of a real tangent map. -/
def complexifiedMapComplex (f : V →ₗ[ℝ] W) :
    (ℂ ⊗[ℝ] V) →ₗ[ℂ] W where
  toFun := complexifiedMap f
  map_add' := (complexifiedMap f).map_add
  map_smul' := complexifiedMap_map_complex_smul f

@[simp] theorem complexifiedMapComplex_tmul (f : V →ₗ[ℝ] W)
    (z : ℂ) (v : V) :
    complexifiedMapComplex f (z ⊗ₜ[ℝ] v) = z • f v := rfl

theorem isInfinitesimalComplexification_iff_bijective_complex
    (f : V →ₗ[ℝ] W) :
    IsInfinitesimalComplexification f ↔
      Function.Bijective (complexifiedMapComplex f) := Iff.rfl

end
end QuaternionicSymmetry.RealToComplexTangentComplexification
