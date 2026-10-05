import QuaternionicSymmetry.LocalConnectionCoordinatePullback

namespace QuaternionicSymmetry.LocalConnectionGaugeDifference
open LocalConnection LocalConnectionCoordinatePullback LocalConnectionGauge
noncomputable section
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

theorem pullback_sub (Γ₁ Γ₀ : Form (E := E) (A := A)) (φ : E → E) :
    pullback (Γ₁ - Γ₀) φ = pullback Γ₁ φ - pullback Γ₀ φ := by
  funext x
  ext v
  rfl

theorem transform_sub (Γ₁ Γ₀ : Form (E := E) (A := A)) (g h : E → A) :
    transform Γ₁ g h - transform Γ₀ g h = adjointForm (Γ₁ - Γ₀) g h := by
  funext x
  ext v
  simp only [Pi.sub_apply, ContinuousLinearMap.sub_apply, transform_apply, adjointForm_apply]
  noncomm_ring

end
end QuaternionicSymmetry.LocalConnectionGaugeDifference
