import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllFiberVerticalSign
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! A source-free real-Fréchet derivative decomposition for a jointly
differentiable map on a product. This is the analytic step that upgrades
separately checked base, moving-frame, and fiber derivatives to the literal
full transition derivative. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointDerivative

noncomputable section

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem fderiv_joint_split (F : X × Y → Z) (x : X) (y : Y)
    (hF : DifferentiableAt ℝ F (x,y)) (u : X) (v : Y) :
    fderiv ℝ F (x,y) (u,v) =
      fderiv ℝ (fun a => F (a,y)) x u +
      fderiv ℝ (fun b => F (x,b)) y v := by
  have hleft := (hF.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)).fderiv
  have hright := (hF.hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)).fderiv
  have hleft' : fderiv ℝ F (x,y) (u,0) =
      fderiv ℝ (fun a => F (a,y)) x u := by
    have hu := congrArg (fun L : X →L[ℝ] Z => L u) hleft
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using hu.symm
  have hright' : fderiv ℝ F (x,y) (0,v) =
      fderiv ℝ (fun b => F (x,b)) y v := by
    have hv := congrArg (fun L : Y →L[ℝ] Z => L v) hright
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using hv.symm
  calc
    fderiv ℝ F (x,y) (u,v) =
        fderiv ℝ F (x,y) ((u,0) + (0,v)) := by simp
    _ = fderiv ℝ F (x,y) (u,0) + fderiv ℝ F (x,y) (0,v) :=
      map_add _ _ _
    _ = _ := by rw [hleft', hright']

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointDerivative
