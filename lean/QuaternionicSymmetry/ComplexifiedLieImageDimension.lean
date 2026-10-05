import QuaternionicSymmetry.ComplexifiedLieSubspaceDimension
import QuaternionicSymmetry.ComplexLieCentralizerRealRange

/-! Dimension and real-image recognition for the actual complexified image
of a real Lie subspace. All maps are specified; no abstract isomorphism or
chosen replacement image is used. -/

namespace QuaternionicSymmetry.ComplexifiedLieImageDimension

open ComplexifiedLieCentralizerComponents ComplexifiedLieSubspaceDimension
  ComplexLieCentralizerRealRange
open scoped TensorProduct
noncomputable section

variable {L V W : Type*} [LieRing L] [LieAlgebra ℝ L]
  [LieRing V] [LieAlgebra ℂ V] [AddCommGroup W] [Module ℝ W]
  (T : Submodule ℝ L) (f : (ℂ ⊗[ℝ] L) →ₗ[ℂ] V)
  (hInj : Function.Injective f)

include hInj

theorem finrank_complexSpan_image :
    Module.finrank ℂ ((complexSpan T).map f) = Module.finrank ℝ T := by
  rw [← (Submodule.equivMapOfInjective f hInj (complexSpan T)).finrank_eq,
    finrank_complexSpan]

theorem complexSpan_image_finiteDimensional [FiniteDimensional ℝ T] :
    FiniteDimensional ℂ ((complexSpan T).map f) := by
  letI : FiniteDimensional ℂ (complexSpan T) := complexSpan_finiteDimensional T
  exact Module.Finite.equiv (Submodule.equivMapOfInjective f hInj (complexSpan T))

theorem finrank_real_complexSpan_image :
    Module.finrank ℝ ((complexSpan T).map f) = 2 * Module.finrank ℝ T := by
  rw [finrank_real_of_complex, finrank_complexSpan_image T f hInj]

theorem real_range_eq_complexSpan_image [FiniteDimensional ℝ T]
    (hSelf : ∀ v : V, v ∈ (complexSpan T).map f ↔
      ∀ s ∈ (complexSpan T).map f, ⁅v,s⁆ = 0)
    (g : W →ₗ[ℝ] V) (hg : Function.Injective g)
    (hCentral : ∀ w s, s ∈ (complexSpan T).map f → ⁅g w,s⁆ = 0)
    (hDim : Module.finrank ℝ W = 2 * Module.finrank ℝ T) :
    LinearMap.range g = ((complexSpan T).map f).restrictScalars ℝ := by
  letI : FiniteDimensional ℂ ((complexSpan T).map f) :=
    complexSpan_image_finiteDimensional T f hInj
  apply range_eq_of_selfCentralizing _ hSelf g hg hCentral
  simpa only [finrank_complexSpan_image T f hInj] using hDim

end
end QuaternionicSymmetry.ComplexifiedLieImageDimension
