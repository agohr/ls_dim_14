import QuaternionicSymmetry.GeneralSmoothInvolutionDerivative
import QuaternionicSymmetry.GeneralLeviCivitaInvariantEndomorphismJet

/-! An actual smooth local involution reflects a smooth endomorphism
field by its derivative. The reflected field is smooth at its fixed
center, agrees there with the original field when the derivative is
`-Id`, and satisfies the exact intertwining law on a neighborhood. -/

namespace QuaternionicSymmetry.GeneralSmoothReflectedEndomorphismField

open Filter
open scoped Topology ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def reflectedField (F : E → E) (A : E → E →L[ℝ] E) (z : E) : E →L[ℝ] E :=
  let R := fderiv ℝ F
  (R (F z)).comp ((A (F z)).comp (R z))

theorem reflectedField_differentiableAt_center
    (F : E → E) (A : E → E →L[ℝ] E) (y : E)
    (hF : ContDiffAt ℝ 2 F y)
    (hcenter : F y = y)
    (hA : DifferentiableAt ℝ A y) :
    DifferentiableAt ℝ (reflectedField F A) y := by
  let R := fderiv ℝ F
  have hFd : DifferentiableAt ℝ F y := hF.differentiableAt (by norm_num)
  have hR : DifferentiableAt ℝ R y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hRF : DifferentiableAt ℝ (R ∘ F) y := by
    have hRF0 : DifferentiableAt ℝ R (F y) := by simpa only [hcenter] using hR
    exact hRF0.comp y hFd
  have hAF : DifferentiableAt ℝ (A ∘ F) y := by
    have hAF0 : DifferentiableAt ℝ A (F y) := by simpa only [hcenter] using hA
    exact hAF0.comp y hFd
  have hAR : DifferentiableAt ℝ (fun z => (A (F z)).comp (R z)) y :=
    hAF.clm_comp hR
  exact hRF.clm_comp hAR

theorem reflectedField_eq_self_center
    (F : E → E) (A : E → E →L[ℝ] E) (y : E)
    (hcenter : F y = y)
    (hneg : ∀ v : E, fderiv ℝ F y v = -v) :
    reflectedField F A y = A y := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [reflectedField, hcenter, ContinuousLinearMap.comp_apply,
    hneg, map_neg, neg_neg]

theorem reflectedField_intertwines_eventually
    (F : E → E) (A : E → E →L[ℝ] E) (y : E)
    (hinv : ∀ᶠ z in 𝓝 y, F (F z) = z)
    (hRinv : ∀ᶠ z in 𝓝 y,
      (fderiv ℝ F (F z)).comp (fderiv ℝ F z) =
        ContinuousLinearMap.id ℝ E) :
    ∀ᶠ z in 𝓝 y, ∀ v : E,
      reflectedField F A (F z) ((fderiv ℝ F z) v) =
        (fderiv ℝ F z) (A z v) := by
  filter_upwards [hinv, hRinv] with z hz hRz v
  have hRv := congrArg (fun L : E →L[ℝ] E => L v) hRz
  change (fderiv ℝ F (F z)) ((fderiv ℝ F z) v) = v at hRv
  simp only [reflectedField, ContinuousLinearMap.comp_apply, hz, hRv]

end
end QuaternionicSymmetry.GeneralSmoothReflectedEndomorphismField
