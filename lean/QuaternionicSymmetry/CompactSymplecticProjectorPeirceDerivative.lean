import QuaternionicSymmetry.CompactSymplecticProjectorActualOrthogonalProjection
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! First Fréchet derivative of the actual ambient Peirce tangent
projection, explicitly retaining the two noncommuting matrix orders. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorPeirceDerivative

open Matrix
open ProjectorPeirceTangentProjection
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem fderiv_tangentPart (n : ℕ) (P A Y : Mat n) :
    fderiv ℝ (fun B : Mat n => tangentPart B A) P Y =
      Y * A + A * Y - 2 • (Y * A * P + P * A * Y) := by
  have hleft : DifferentiableAt ℝ (fun B : Mat n => B * A) P := by fun_prop
  have hright : DifferentiableAt ℝ (fun B : Mat n => A * B) P := by fun_prop
  have hprod : DifferentiableAt ℝ (fun B : Mat n => B * A * B) P := by fun_prop
  have hlinearLeft : fderiv ℝ (fun B : Mat n => B * A) P Y = Y * A := by
    have h := congrArg (fun L : Mat n →L[ℝ] Mat n => L Y)
      (fderiv_mul_const' (a := id) (x := P) differentiableAt_id A)
    simpa only [fderiv_id, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, op_smul_eq_mul] using h
  have hlinearRight : fderiv ℝ (fun B : Mat n => A * B) P Y = A * Y := by
    have h := congrArg (fun L : Mat n →L[ℝ] Mat n => L Y)
      (fderiv_const_mul (a := id) (x := P) differentiableAt_id A)
    simpa only [fderiv_id, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] using h
  have hprodD : fderiv ℝ (fun B : Mat n => B * A * B) P Y =
      Y * A * P + P * A * Y := by
    have h := fderiv_fun_mul' (a := fun B : Mat n => B * A) (b := id)
      hleft differentiableAt_id
    change fderiv ℝ (fun B : Mat n => B * A * B) P = _ at h
    rw [h]
    simp only [ContinuousLinearMap.add_apply, fderiv_id,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply,
      op_smul_eq_mul, smul_eq_mul, hlinearLeft]
    change P * A * Y + Y * A * P = Y * A * P + P * A * Y
    abel
  change fderiv ℝ (fun B : Mat n => B * A + A * B - 2 • (B * A * B)) P Y = _
  change (fderiv ℝ
    (((fun B : Mat n => B * A) + (fun B : Mat n => A * B)) -
      2 • (fun B : Mat n => B * A * B)) P) Y = _
  rw [fderiv_sub (hleft.add hright) (hprod.const_smul 2)]
  rw [fderiv_add hleft hright, fderiv_const_smul hprod]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, hlinearLeft, hlinearRight, hprodD]

end
end QuaternionicSymmetry.CompactSymplecticProjectorPeirceDerivative
