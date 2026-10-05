import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Real and imaginary component maps for the literal complexification
`ℂ ⊗[ℝ] L`. They will separate two real bracket equations when proving
centralizer transfer for a maximal compact torus. -/

namespace QuaternionicSymmetry.ComplexTensorRealImagComponents

open scoped TensorProduct
noncomputable section

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

def realComponent : (ℂ ⊗[ℝ] L) →ₗ[ℝ] L :=
  (TensorProduct.lid ℝ L).toLinearMap.comp
    (TensorProduct.map Complex.reLm (LinearMap.id : L →ₗ[ℝ] L))

def imagComponent : (ℂ ⊗[ℝ] L) →ₗ[ℝ] L :=
  (TensorProduct.lid ℝ L).toLinearMap.comp
    (TensorProduct.map Complex.imLm (LinearMap.id : L →ₗ[ℝ] L))

@[simp] theorem realComponent_tmul (z : ℂ) (v : L) :
    realComponent (z ⊗ₜ[ℝ] v) = z.re • v := by
  simp [realComponent, Complex.reLm_coe]

@[simp] theorem imagComponent_tmul (z : ℂ) (v : L) :
    imagComponent (z ⊗ₜ[ℝ] v) = z.im • v := by
  simp [imagComponent, Complex.imLm_coe]

/-- Every complexified real vector has its literal real and imaginary
tensor components. -/
theorem eq_one_tmul_add_I_tmul (t : ℂ ⊗[ℝ] L) :
    t = (1 : ℂ) ⊗ₜ[ℝ] realComponent t + Complex.I ⊗ₜ[ℝ] imagComponent t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul z v =>
      simp only [realComponent_tmul, imagComponent_tmul]
      calc
        z ⊗ₜ[ℝ] v = ((z.re : ℂ) + z.im * Complex.I) ⊗ₜ[ℝ] v := by
          rw [Complex.re_add_im]
        _ = (1 : ℂ) ⊗ₜ[ℝ] (z.re • v) +
              Complex.I ⊗ₜ[ℝ] (z.im • v) := by
          rw [TensorProduct.add_tmul]
          congr 1
          · rw [← TensorProduct.smul_tmul]
            simp only [Complex.real_smul, mul_one]
          · rw [← TensorProduct.smul_tmul]
            simp only [Complex.real_smul, mul_comm]
  | add x y hx hy =>
      calc
        x + y =
            ((1 : ℂ) ⊗ₜ[ℝ] realComponent x +
              Complex.I ⊗ₜ[ℝ] imagComponent x) +
            ((1 : ℂ) ⊗ₜ[ℝ] realComponent y +
              Complex.I ⊗ₜ[ℝ] imagComponent y) :=
          congrArg₂ (· + ·) hx hy
        _ = (1 : ℂ) ⊗ₜ[ℝ] realComponent (x + y) +
              Complex.I ⊗ₜ[ℝ] imagComponent (x + y) := by
          rw [realComponent.map_add, imagComponent.map_add,
            TensorProduct.tmul_add, TensorProduct.tmul_add]
          abel

end
end QuaternionicSymmetry.ComplexTensorRealImagComponents
