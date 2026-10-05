import QuaternionicSymmetry.GeneralConnectionGaugePullback

/-! A connection gauge transform only uses the gauge value, its first
derivative, the inverse-gauge value, and the form value at the point. -/

namespace QuaternionicSymmetry.GeneralConnectionGaugeLocalCongruence

open Filter LocalConnectionGauge
open scoped Topology
noncomputable section

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

theorem transform_congr_at
    (Γ₁ Γ₂ : LocalConnection.Form (E := E) (A := A))
    (g₁ g₂ h₁ h₂ : E → A) (y : E)
    (hΓ : Γ₁ y = Γ₂ y)
    (hg : g₁ =ᶠ[𝓝 y] g₂)
    (hh : h₁ y = h₂ y) :
    transform Γ₁ g₁ h₁ y = transform Γ₂ g₂ h₂ y := by
  ext v
  simp only [transform_apply, hΓ, hh, hg.eq_of_nhds,
    hg.fderiv_eq]

end
end QuaternionicSymmetry.GeneralConnectionGaugeLocalCongruence
