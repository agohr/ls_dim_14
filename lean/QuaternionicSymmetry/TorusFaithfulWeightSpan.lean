import QuaternionicSymmetry.QuaternionicTorusWeightKernel
import QuaternionicSymmetry.SelectedTorusCompactExponentialSmooth
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A faithful standard compact-torus diagonal representation has
real-spanning integral weights. The proof detects the common real kernel
along the literal coordinate circle exponential. This says nothing about
weights of a different, unpowered contact line. -/

namespace QuaternionicSymmetry.TorusFaithfulWeightSpan

open ManifoldQuaternionicTorusAction
open SelectedTorusCompactExponentialSmooth
open scoped BigOperators
noncomputable section

variable {r : ℕ}

/-- The real functional of an integral character on the standard torus. -/
def integralWeightLinear (μ : Fin r → ℤ) : Module.Dual ℝ (Fin r → ℝ) where
  toFun u := ∑ i, (μ i : ℝ) * u i
  map_add' u v := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [RingHom.id_apply]
    ring

theorem integralWeightLinear_apply (μ : Fin r → ℤ) (u : Fin r → ℝ) :
    integralWeightLinear μ u = ∑ i, (μ i : ℝ) * u i := rfl

/-- Finite-dimensional duality: a family of weight functionals spans the
whole real dual exactly when it has no common nonzero real direction. -/
theorem integralWeight_span_top_of_common_kernel_zero {ι : Type*}
    (μ : ι → Fin r → ℤ)
    (hKer : ∀ u : Fin r → ℝ,
      (∀ j : ι, integralWeightLinear (μ j) u = 0) → u = 0) :
    Submodule.span ℝ (Set.range (fun j => integralWeightLinear (μ j))) = ⊤ := by
  let W : Submodule ℝ (Module.Dual ℝ (Fin r → ℝ)) :=
    Submodule.span ℝ (Set.range (fun j => integralWeightLinear (μ j)))
  have hCoann : W.dualCoannihilator = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    apply hKer u
    intro j
    exact hu (integralWeightLinear (μ j))
      (Submodule.subset_span ⟨j,rfl⟩)
  have hDouble : W.dualCoannihilator.dualAnnihilator = W :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  simpa only [hCoann, Submodule.dualAnnihilator_bot] using hDouble.symm

end
end QuaternionicSymmetry.TorusFaithfulWeightSpan
