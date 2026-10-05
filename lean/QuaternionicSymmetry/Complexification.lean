import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Analysis.Complex.Basic

/-! A real-part retraction from the complexification tensor algebra. -/

namespace QuaternionicSymmetry.Complexification

open scoped TensorProduct

noncomputable section

variable {S : Type*} [CommRing S] [Algebra ℝ S]

/-- The real part on `ℂ ⊗[ℝ] S`, obtained by applying complex real part to
the first tensor factor and then the canonical `ℝ ⊗[ℝ] S ≃ₗ S`. -/
def realPart : (ℂ ⊗[ℝ] S) →ₗ[ℝ] S :=
  (TensorProduct.lid ℝ S).toLinearMap.comp
    (TensorProduct.map Complex.reLm (LinearMap.id : S →ₗ[ℝ] S))

@[simp] theorem realPart_tmul (z : ℂ) (s : S) :
    realPart (z ⊗ₜ[ℝ] s) = z.re • s := by
  rw [realPart, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  change TensorProduct.lid ℝ S (z.re ⊗ₜ[ℝ] s) = _
  rw [TensorProduct.lid_tmul]

@[simp] theorem realPart_includeRight (s : S) :
    realPart (Algebra.TensorProduct.includeRight s) = s := by
  rw [Algebra.TensorProduct.includeRight_apply, realPart_tmul]
  simp

theorem includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight :
      S →ₐ[ℝ] ℂ ⊗[ℝ] S) := by
  intro x y h
  apply_fun realPart at h
  simpa using h

end
end QuaternionicSymmetry.Complexification
