import QuaternionicSymmetry.GeneralImmersionProjectionDerivative

/-! Differential of a genuinely idempotent ambient projection field;
in particular, the derivative sends normal vectors into its image. -/

namespace QuaternionicSymmetry.GeneralImmersionProjectionIdempotentDerivative

open scoped Topology
noncomputable section

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem projection_idempotent_derivative
    (proj : E → V →L[ℝ] V) (y u : E) (A : V)
    (hproj : DifferentiableAt ℝ proj y)
    (hid : ∀ z B, proj z (proj z B) = proj z B) :
    (fderiv ℝ proj y u) (proj y A) +
      proj y ((fderiv ℝ proj y u) A) =
        (fderiv ℝ proj y u) A := by
  have hinner : DifferentiableAt ℝ (fun z => proj z A) y :=
    hproj.clm_apply (differentiableAt_const _)
  have hfun : (fun z => proj z (proj z A)) = fun z => proj z A :=
    funext (fun z => hid z A)
  have hd : fderiv ℝ (fun z => proj z (proj z A)) y u =
      fderiv ℝ (fun z => proj z A) y u :=
    congrArg (fun f : E → V => fderiv ℝ f y u) hfun
  rw [fderiv_clm_apply hproj hinner,
    fderiv_clm_apply hproj (differentiableAt_const A)] at hd
  simpa [add_comm] using hd

theorem projection_derivative_normal_is_tangent
    (proj : E → V →L[ℝ] V) (y u : E) (A : V)
    (hproj : DifferentiableAt ℝ proj y)
    (hid : ∀ z B, proj z (proj z B) = proj z B)
    (hA : proj y A = 0) :
    proj y ((fderiv ℝ proj y u) A) = (fderiv ℝ proj y u) A := by
  have h := projection_idempotent_derivative proj y u A hproj hid
  rw [hA, map_zero, zero_add] at h
  exact h

end
end QuaternionicSymmetry.GeneralImmersionProjectionIdempotentDerivative
