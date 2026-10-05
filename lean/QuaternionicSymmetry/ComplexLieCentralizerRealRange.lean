import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! An actual injective real-linear map onto a self-centralizing complex
Lie subspace is determined by centralization and dimension. This identifies
the real image, not the complex linearity of the map or holomorphicity of
any parametrization. -/

namespace QuaternionicSymmetry.ComplexLieCentralizerRealRange

noncomputable section

variable {W V : Type*} [AddCommGroup W] [Module ℝ W]
  [LieRing V] [LieAlgebra ℂ V]

theorem range_eq_restrictScalars_of_finrank
    (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (g : W →ₗ[ℝ] V) (hInj : Function.Injective g)
    (hMem : ∀ w, g w ∈ S)
    (hDim : Module.finrank ℝ W = 2 * Module.finrank ℂ S) :
    LinearMap.range g = S.restrictScalars ℝ := by
  let e := (Submodule.restrictScalarsEquiv ℝ ℂ V S).restrictScalars ℝ
  letI : FiniteDimensional ℝ (S.restrictScalars ℝ) :=
    Module.Finite.equiv e.symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨w, rfl⟩
    exact hMem w
  · rw [LinearMap.finrank_range_of_inj hInj, e.finrank_eq,
      finrank_real_of_complex, hDim]

theorem range_eq_of_selfCentralizing
    (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (hSelf : ∀ v : V, v ∈ S ↔ ∀ s ∈ S, ⁅v,s⁆ = 0)
    (g : W →ₗ[ℝ] V) (hInj : Function.Injective g)
    (hCentral : ∀ w s, s ∈ S → ⁅g w,s⁆ = 0)
    (hDim : Module.finrank ℝ W = 2 * Module.finrank ℂ S) :
    LinearMap.range g = S.restrictScalars ℝ :=
  range_eq_restrictScalars_of_finrank S g hInj
    (fun w => (hSelf (g w)).mpr (hCentral w)) hDim

theorem smul_mem_range_of_selfCentralizing
    (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (hSelf : ∀ v : V, v ∈ S ↔ ∀ s ∈ S, ⁅v,s⁆ = 0)
    (g : W →ₗ[ℝ] V) (hInj : Function.Injective g)
    (hCentral : ∀ w s, s ∈ S → ⁅g w,s⁆ = 0)
    (hDim : Module.finrank ℝ W = 2 * Module.finrank ℂ S)
    (c : ℂ) {v : V} (hv : v ∈ LinearMap.range g) :
    c • v ∈ LinearMap.range g := by
  rw [range_eq_of_selfCentralizing S hSelf g hInj hCentral hDim] at hv ⊢
  exact S.smul_mem c hv

end
end QuaternionicSymmetry.ComplexLieCentralizerRealRange
