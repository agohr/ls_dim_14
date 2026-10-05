import QuaternionicSymmetry.LocalConnection

/-! Curvature of a sum of commuting local connection forms. -/
namespace QuaternionicSymmetry.LocalConnection

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

theorem curvature_add_of_commuting (Γ θ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x)
    (hcomm : ∀ u v, Γ x u * θ x v = θ x v * Γ x u) :
    curvature (Γ + θ) x = curvature Γ x + curvature θ x := by
  ext u v
  simp only [curvature_apply, fderiv_add hΓ hθ, ContinuousLinearMap.add_apply,
    Pi.add_apply, add_mul, mul_add]
  rw [hcomm u v, hcomm v u]
  abel

end QuaternionicSymmetry.LocalConnection
