import QuaternionicSymmetry.RealToComplexTangentComplexificationLinear

/-! Equality of genuine complex-linear characters on a real derivative
extends to equality on its literal scalar-extension tensor product. -/

namespace QuaternionicSymmetry.RealCharacterComplexificationCompatibility

open RealToComplexTangentComplexification
open scoped TensorProduct
noncomputable section

variable {U H : Type*} [AddCommGroup U] [Module ℝ U]
  [AddCommGroup H] [Module ℂ H]

theorem complexified_character_comp
    (f : U →ₗ[ℝ] H) (χ : H →ₗ[ℂ] ℂ) (β : U →ₗ[ℝ] ℂ)
    (hCompat : ∀ u, χ (f u) = β u) :
    χ.comp (complexifiedMapComplex f) = complexifiedMapComplex β := by
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul z u => simp [hCompat, map_smul]
  | add x y hx hy =>
      change χ ((complexifiedMapComplex f) x) = (complexifiedMapComplex β) x at hx
      change χ ((complexifiedMapComplex f) y) = (complexifiedMapComplex β) y at hy
      simpa only [LinearMap.comp_apply, map_add] using congrArg₂ (· + ·) hx hy

end
end QuaternionicSymmetry.RealCharacterComplexificationCompatibility
