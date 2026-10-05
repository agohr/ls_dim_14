import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! A smooth map that squares to the identity on a neighborhood has
mutually inverse derivatives at paired nearby points. This is derived
from the actual local identity, not assumed as an inverse chart field. -/

namespace QuaternionicSymmetry.GeneralSmoothInvolutionDerivative

open Filter
open scoped Topology ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem derivative_comp_of_eventual_involution
    (F : E → E) (x : E)
    (hF : ContDiffAt ℝ 1 F x)
    (hcenter : F x = x)
    (hinv : ∀ᶠ y in 𝓝 x, F (F y) = y) :
    ∀ᶠ y in 𝓝 x,
      (fderiv ℝ F (F y)).comp (fderiv ℝ F y) =
        ContinuousLinearMap.id ℝ E := by
  let U : Set E := {y | F (F y) = y}
  have hU : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hinv
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y :=
    (hF.eventually (by norm_num)).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have hdiffF : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F (F y) := by
    have hc : ContinuousAt F x := hF.continuousAt
    have hdiffAtFx : ∀ᶠ y in 𝓝 (F x), DifferentiableAt ℝ F y := by
      simpa only [hcenter] using hdiff
    exact hc.eventually hdiffAtFx
  filter_upwards [(isOpen_interior.mem_nhds hU), hdiff, hdiffF]
    with y hy hdy hdFy
  have hlocal : (F ∘ F) =ᶠ[𝓝 y] id := by
    filter_upwards [(isOpen_interior.mem_nhds hy)] with z hz
    change F (F z) = z
    exact (interior_subset : interior U ⊆ U) hz
  have hd := hlocal.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp y hdFy hdy] at hd
  simpa only [fderiv_id] using hd

end
end QuaternionicSymmetry.GeneralSmoothInvolutionDerivative
