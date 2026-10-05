import QuaternionicSymmetry.AlgebraicLeviCivitaUniqueness
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Metricity and symmetry of the covariant Hessian of an isometric
immersion, in arbitrary source and target orthonormal frames. -/
namespace QuaternionicSymmetry.ImmersionHessianCalculus

open Filter
open scoped ContDiff Topology
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Rectangular version of infinitesimal orthogonality. -/
theorem fderiv_isometric_skew
    (A : F → (F →L[ℝ] E)) (y : F)
    (hA : DifferentiableAt ℝ A y)
    (hiso : ∀ᶠ z in 𝓝 y, ∀ v w : F,
      inner ℝ (A z v) (A z w) = inner ℝ v w) (u v w : F) :
    inner ℝ ((fderiv ℝ A y u) v) (A y w) +
      inner ℝ (A y v) ((fderiv ℝ A y u) w) = 0 := by
  have hv := hA.clm_apply (differentiableAt_const v)
  have hw := hA.clm_apply (differentiableAt_const w)
  have heq : (fun z => inner ℝ (A z v) (A z w)) =ᶠ[𝓝 y]
      (fun _ => inner ℝ v w) := by
    filter_upwards [hiso] with z hz; exact hz v w
  have hd := congrArg (fun T : F →L[ℝ] ℝ => T u) heq.fderiv_eq
  rw [fderiv_const_apply] at hd
  change (fderiv ℝ (fun z => inner ℝ (A z v) (A z w)) y) u = 0 at hd
  rw [fderiv_inner_apply (𝕜 := ℝ) hv hw u,
    fderiv_clm_apply hA (differentiableAt_const v),
    fderiv_clm_apply hA (differentiableAt_const w)] at hd
  simpa only [fderiv_const_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.flip_apply, map_zero, zero_add, add_comm] using hd

def hessian (A : F → F →L[ℝ] E) (G : F → E) (y : F)
    (ΓP : E →L[ℝ] E →L[ℝ] E) (ΓR : F →L[ℝ] F →L[ℝ] F)
    (u v : F) : E :=
  (fderiv ℝ A y u) v + ΓP (fderiv ℝ G y u) (A y v) - A y (ΓR u v)

/-- Differentiating the isometry identity gives the metric identity for
the covariant Hessian. -/
theorem hessian_metric
    (A : F → F →L[ℝ] E) (G : F → E) (y : F)
    (ΓP : E →L[ℝ] E →L[ℝ] E) (ΓR : F →L[ℝ] F →L[ℝ] F)
    (hA : DifferentiableAt ℝ A y)
    (hiso : ∀ᶠ z in 𝓝 y, ∀ v w : F,
      inner ℝ (A z v) (A z w) = inner ℝ v w)
    (hP : ∀ u v w, inner ℝ (ΓP u v) w + inner ℝ v (ΓP u w) = 0)
    (hR : ∀ u v w, inner ℝ (ΓR u v) w + inner ℝ v (ΓR u w) = 0)
    (u v w : F) :
    inner ℝ (hessian A G y ΓP ΓR u v) (A y w) +
      inner ℝ (A y v) (hessian A G y ΓP ΓR u w) = 0 := by
  have hdiff := fderiv_isometric_skew A y hA hiso u v w
  have hpoint := hiso.self_of_nhds
  have ht := hP (fderiv ℝ G y u) (A y v) (A y w)
  have hs := hR u v w
  simp only [hessian, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right, hpoint] at ⊢
  linarith

/-- Differentiate the actual solder covariance, retaining the symmetric
second derivative of the chart map. -/
theorem solder_covariance_derivative
    (A : F → F →L[ℝ] E) (S : F → F →L[ℝ] F)
    (T : E → E →L[ℝ] E) (G : F → E) (y : F)
    (hA : DifferentiableAt ℝ A y) (hS : DifferentiableAt ℝ S y)
    (hT : DifferentiableAt ℝ T (G y)) (hG : ContDiffAt ℝ 2 G y)
    (hcov : (fun z => (A z).comp (S z)) =ᶠ[𝓝 y]
      (fun z => (T (G z)).comp (fderiv ℝ G z))) (u v : F) :
    (fderiv ℝ A y u) (S y v) + A y (fderiv ℝ S y u v) =
      (fderiv ℝ T (G y) (fderiv ℝ G y u)) (fderiv ℝ G y v) +
        T (G y) (fderiv ℝ (fderiv ℝ G) y u v) := by
  have hG₁ := hG.differentiableAt (by norm_num)
  have hG₂ := (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hTG : DifferentiableAt ℝ (fun z => T (G z)) y := hT.comp y hG₁
  have hd := congrArg (fun L : F →L[ℝ] (F →L[ℝ] E) => L u v) hcov.fderiv_eq
  rw [fderiv_clm_comp hA hS, fderiv_clm_comp hTG hG₂] at hd
  have hc : fderiv ℝ (fun z => T (G z)) y =
      (fderiv ℝ T (G y)).comp (fderiv ℝ G y) := fderiv_comp y hT hG₁
  rw [hc] at hd
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, add_comm] using hd

/-- Torsion freeness and the chain rule make the Hessian symmetric after
the second argument is put into its orthonormal frame. -/
theorem hessian_symmetric
    (A : F → F →L[ℝ] E) (S : F → F →L[ℝ] F)
    (T : E → E →L[ℝ] E) (G : F → E) (y : F)
    (ΓP : E →L[ℝ] E →L[ℝ] E) (ΓR : F →L[ℝ] F →L[ℝ] F)
    (hA : DifferentiableAt ℝ A y) (hS : DifferentiableAt ℝ S y)
    (hT : DifferentiableAt ℝ T (G y)) (hG : ContDiffAt ℝ 2 G y)
    (hcov : (fun z => (A z).comp (S z)) =ᶠ[𝓝 y]
      (fun z => (T (G z)).comp (fderiv ℝ G z)))
    (hP : ∀ u v, fderiv ℝ T (G y) u v - fderiv ℝ T (G y) v u +
      ΓP u (T (G y) v) - ΓP v (T (G y) u) = 0)
    (hR : ∀ u v, fderiv ℝ S y u v - fderiv ℝ S y v u +
      ΓR u (S y v) - ΓR v (S y u) = 0)
    (u v : F) :
    hessian A G y ΓP ΓR u (S y v) = hessian A G y ΓP ΓR v (S y u) := by
  have h₁ := solder_covariance_derivative A S T G y hA hS hT hG hcov u v
  have h₂ := solder_covariance_derivative A S T G y hA hS hT hG hcov v u
  have hsym := hG.isSymmSndFDerivAt (by simp)
  rw [hsym.eq v u] at h₂
  have hc (w : F) : A y (S y w) = T (G y) (fderiv ℝ G y w) :=
    congrArg (fun L : F →L[ℝ] E => L w) hcov.self_of_nhds
  have ht := hP (fderiv ℝ G y u) (fderiv ℝ G y v)
  have hs := congrArg (A y) (hR u v)
  simp only [map_zero, map_sub, map_add] at hs
  apply sub_eq_zero.mp
  simp only [hessian, hc]
  linear_combination (norm := module) h₁ - h₂ + ht - hs

end
end QuaternionicSymmetry.ImmersionHessianCalculus
