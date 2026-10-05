import QuaternionicSymmetry.ProjectorPeirceTangentProjection
import QuaternionicSymmetry.CompactSymplecticProjectorTangentConstraints

/-! The Peirce projection fixes the derivative of any differentiable
chartwise family of genuine matrix idempotents. -/

namespace QuaternionicSymmetry.ProjectorPeirceChartDerivative

open Matrix ProjectorPeirceTangentProjection
open scoped Matrix.Norms.Operator ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem chart_derivative_peirce_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (F : E → Mat n) (y v : E)
    (hF : DifferentiableAt ℝ F y)
    (hid : ∀ z, F z * F z = F z) :
    F y * (fderiv ℝ F y v) + (fderiv ℝ F y v) * F y =
      fderiv ℝ F y v := by
  have hfun : (fun A : Mat n => A * A) ∘ F = F := funext hid
  have hsqd : DifferentiableAt ℝ (fun A : Mat n => A * A) (F y) := by
    fun_prop
  have hd := fderiv_comp y hsqd hF
  change fderiv ℝ ((fun A : Mat n => A * A) ∘ F) y = _ at hd
  rw [hfun] at hd
  have hv := congrArg (fun D : E →L[ℝ] Mat n => D v) hd
  have hmul := fderiv_fun_mul' (a := id) (b := id)
    (differentiableAt_id : DifferentiableAt ℝ (id : Mat n → Mat n) (F y))
    differentiableAt_id
  change fderiv ℝ (fun A : Mat n => A * A) (F y) = _ at hmul
  rw [hmul] at hv
  simpa [fderiv_id, MulOpposite.op_smul] using hv.symm

theorem chart_derivative_peirce_fixed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (F : E → Mat n) (y v : E)
    (hF : DifferentiableAt ℝ F y)
    (hid : ∀ z, F z * F z = F z) :
    tangentPart (F y) (fderiv ℝ F y v) = fderiv ℝ F y v :=
  tangentPart_eq_self_of_tangent (F y) (fderiv ℝ F y v) (hid y)
    (chart_derivative_peirce_tangent n F y v hF hid)

end
end QuaternionicSymmetry.ProjectorPeirceChartDerivative
