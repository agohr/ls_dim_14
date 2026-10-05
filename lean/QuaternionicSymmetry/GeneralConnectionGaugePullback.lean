import QuaternionicSymmetry.LocalConnectionGauge
import QuaternionicSymmetry.LocalConnectionCoordinatePullback

/-! Gauge transformation of a local connection commutes with genuine
coordinate pullback, by the Fréchet chain rule. -/

namespace QuaternionicSymmetry.GeneralConnectionGaugePullback

open LocalConnectionGauge LocalConnectionCoordinatePullback
open scoped Topology
noncomputable section

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

theorem pullback_transform
    (Γ : LocalConnection.Form (E := E) (A := A))
    (g h : E → A) (φ : E → E) (y : E)
    (hφ : DifferentiableAt ℝ φ y)
    (hg : DifferentiableAt ℝ g (φ y)) :
    pullback (transform Γ g h) φ y =
      transform (pullback Γ φ) (g ∘ φ) (h ∘ φ) y := by
  ext u
  simp only [pullback, transform_apply,
    ContinuousLinearMap.comp_apply, Function.comp_apply]
  rw [fderiv_comp y hg hφ]
  rfl

end
end QuaternionicSymmetry.GeneralConnectionGaugePullback
