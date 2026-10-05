import QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap

/-! Elementary affine-gauge covariance of the endomorphism covariant
derivative, stated independently of any model geometry. -/

namespace QuaternionicSymmetry.GeneralAdaptedGaugeAdjointCovariance

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem affine_adjoint_identity
    (g h Λ dg Γ T dh : E →L[ℝ] E)
    (hgh : g * h = 1)
    (hΓ : Γ = h * (Λ * g + dg))
    (hdh : dh = -(h * dg * h)) :
    g * (Γ * T - T * Γ) * h =
      Λ * (g * T * h) - (g * T * h) * Λ +
        (dg * T * h + g * T * dh) := by
  subst Γ
  subst dh
  simp only [mul_add, add_mul, mul_sub, sub_mul,
    mul_neg, mul_assoc]
  simp only [← mul_assoc g h, hgh, one_mul]
  noncomm_ring

end
end QuaternionicSymmetry.GeneralAdaptedGaugeAdjointCovariance
