import QuaternionicSymmetry.ManifoldQuaternionicConnectionIsometrySolder
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Differentiating the verified orthogonality of an adapted isometry matrix
gives the skew relation needed for pullback-connection metricity. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryDerivativeSkew

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A differentiable orthogonal matrix field has skew infinitesimal
variation relative to its value at the point. -/
theorem fderiv_orthogonal_skew
    (U : E → (E →L[ℝ] E)) (y : E)
    (hU : DifferentiableAt ℝ U y)
    (horth : ∀ᶠ z in nhds y, ∀ v w : E,
      inner ℝ (U z v) (U z w) = inner ℝ v w)
    (u v w : E) :
    inner ℝ ((fderiv ℝ U y u) v) (U y w) +
      inner ℝ (U y v) ((fderiv ℝ U y u) w) = 0 := by
  have hv : DifferentiableAt ℝ (fun z : E => U z v) y :=
    hU.clm_apply (differentiableAt_const v)
  have hw : DifferentiableAt ℝ (fun z : E => U z w) y :=
    hU.clm_apply (differentiableAt_const w)
  have heq : (fun z : E => inner ℝ (U z v) (U z w)) =ᶠ[nhds y]
      (fun _ => inner ℝ v w) := by
    filter_upwards [horth] with z hz
    exact hz v w
  have hd := congrArg (fun A : E →L[ℝ] ℝ => A u)
    (heq.fderiv_eq (𝕜 := ℝ))
  have hc : fderiv ℝ (fun _ : E => inner ℝ v w) y = 0 := by
    simp
  rw [hc] at hd
  change (fderiv ℝ (fun z : E => inner ℝ (U z v) (U z w)) y) u = 0 at hd
  rw [fderiv_inner_apply (𝕜 := ℝ) hv hw u] at hd
  rw [fderiv_clm_apply hU (differentiableAt_const v),
    fderiv_clm_apply hU (differentiableAt_const w)] at hd
  have hvc : fderiv ℝ (fun _ : E => v) y = 0 := by
    simp
  have hwc : fderiv ℝ (fun _ : E => w) y = 0 := by
    simp
  rw [hvc, hwc] at hd
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply,
    map_zero, zero_add, add_comm] using hd

end QuaternionicSymmetry.ManifoldQuaternionicIsometryDerivativeSkew
