import QuaternionicSymmetry.GeneralAdaptedGaugeAdjointCovariance
import QuaternionicSymmetry.ManifoldQuaternionicCommutatorSpan

/-! The affine connection law carries preservation of a quaternionic
operator span backward across an invertible, differentiable gauge. -/

namespace QuaternionicSymmetry.GeneralAdaptedQuaternionicSpanDescent

open VectorBundleFrameTransitions
open GeneralAdaptedGaugeAdjointCovariance
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem affine_quaternionic_span_descent
    (Qp Qq : QuaternionicStructure E)
    (g h Λ dg Γ T dh dT : E →L[ℝ] E)
    (hgh : g * h = 1) (hhg : h * g = 1)
    (hΓ : Γ = h * (Λ * g + dg))
    (hdh : dh = -(h * dg * h))
    (hTq : g * T * h ∈ quaternionicSpan Qq)
    (hcomm : Λ * (g * T * h) - (g * T * h) * Λ ∈ quaternionicSpan Qq)
    (hderiv : dT = dg * T * h + g * T * dh)
    (hdT : dT ∈ quaternionicSpan Qq)
    (hback : ∀ U ∈ quaternionicSpan Qq,
      h * U * g ∈ quaternionicSpan Qp) :
    Γ * T - T * Γ ∈ quaternionicSpan Qp := by
  have hforward : g * (Γ * T - T * Γ) * h ∈ quaternionicSpan Qq := by
    rw [affine_adjoint_identity g h Λ dg Γ T dh hgh hΓ hdh]
    rw [← hderiv]
    exact (quaternionicSpan Qq).add_mem hcomm hdT
  have := hback _ hforward
  convert this using 1
  simp only [mul_assoc, ← mul_assoc h g, hhg, one_mul,
    ← mul_assoc (Γ * T - T * Γ) h, hgh, mul_one]

end
end QuaternionicSymmetry.GeneralAdaptedQuaternionicSpanDescent
