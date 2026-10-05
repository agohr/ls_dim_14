import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! A zero-valued differentiable section of a smoothly varying projected
subspace has derivative inside the fiber at its zero. -/

namespace QuaternionicSymmetry.GeneralSmoothZeroSectionDerivative

open Filter
open scoped Topology
noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem zero_section_fderiv_mem
    (P : E → V →L[ℝ] V) (s : E → V)
    (K : Submodule ℝ V) (y u : E)
    (hP : DifferentiableAt ℝ P y)
    (hs : DifferentiableAt ℝ s y)
    (hzero : s y = 0)
    (hfix : ∀ᶠ z in 𝓝 y, P z (s z) = s z)
    (hrange : ∀ v, P y v ∈ K) :
    (fderiv ℝ s y) u ∈ K := by
  have heq0 : (fun z => P z (s z)) =ᶠ[𝓝 y] s := hfix
  have heq : fderiv ℝ (fun z => P z (s z)) y = fderiv ℝ s y :=
    heq0.fderiv_eq
  rw [fderiv_clm_apply hP hs] at heq
  have happly := congrArg (fun T : E →L[ℝ] V => T u) heq
  simp only [ContinuousLinearMap.comp_apply, hzero, map_zero, add_zero] at happly
  rw [← happly]
  exact hrange _

end
end QuaternionicSymmetry.GeneralSmoothZeroSectionDerivative
