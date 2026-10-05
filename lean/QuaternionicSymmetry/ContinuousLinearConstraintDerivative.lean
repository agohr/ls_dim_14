import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Const

/-! A constant continuous linear constraint holding near a point also
annihilates the actual derivative there. -/
namespace QuaternionicSymmetry.ContinuousLinearConstraintDerivative
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem annihilates_fderiv (L : F →L[ℝ] G) (f : E → F) (x u : E)
    (hd : DifferentiableAt ℝ f x) (h : ∀ᶠ z in 𝓝 x, L (f z) = 0) :
    L (fderiv ℝ f x u) = 0 := by
  have he : (fun z => L (f z)) =ᶠ[𝓝 x] (fun _ => (0 : G)) := h
  have hder : fderiv ℝ (fun z => L (f z)) x = fderiv ℝ (fun _ : E => (0 : G)) x :=
    he.fderiv_eq
  rw [fderiv_const_apply] at hder
  have hc : fderiv ℝ (fun z => L (f z)) x = L.comp (fderiv ℝ f x) := by
    simpa only [L.fderiv] using fderiv_comp x (g := L) L.differentiableAt hd
  rw [hc] at hder
  exact congrArg (fun T : E →L[ℝ] G => T u) hder

end QuaternionicSymmetry.ContinuousLinearConstraintDerivative
