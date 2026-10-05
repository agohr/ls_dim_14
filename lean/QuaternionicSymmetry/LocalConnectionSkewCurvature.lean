import QuaternionicSymmetry.LocalConnection
import QuaternionicSymmetry.ContinuousLinearConstraintDerivative
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Skewness of curvature of an actual local metric connection. -/
namespace QuaternionicSymmetry.LocalConnection
open ContinuousLinearConstraintDerivative
open scoped Topology
noncomputable section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def skewPairing (v w : V) : (V →L[ℝ] V) →L[ℝ] ℝ :=
  (innerSL ℝ w).comp (ContinuousLinearMap.apply ℝ V v) +
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ V w)

theorem skewPairing_apply (v w : V) (A : V →L[ℝ] V) :
    skewPairing v w A = inner ℝ (A v) w + inner ℝ v (A w) := by
  change inner ℝ w (A v) + inner ℝ v (A w) = _
  rw [real_inner_comm w (A v)]

theorem commutator_skew (A B : V →L[ℝ] V)
    (hA : ∀ v w, inner ℝ (A v) w + inner ℝ v (A w) = 0)
    (hB : ∀ v w, inner ℝ (B v) w + inner ℝ v (B w) = 0) (v w : V) :
    inner ℝ ((A * B - B * A) v) w + inner ℝ v ((A * B - B * A) w) = 0 := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    inner_sub_left, inner_sub_right]
  linarith [hA (B v) w, hB v (A w), hB (A v) w, hA v (B w)]

theorem fderiv_form_skew (Γ : Form (E := E) (A := V →L[ℝ] V)) (x u t : E)
    (hd : DifferentiableAt ℝ Γ x)
    (hskew : ∀ᶠ z in 𝓝 x, ∀ t v w,
      inner ℝ (Γ z t v) w + inner ℝ v (Γ z t w) = 0) (v w : V) :
    inner ℝ (fderiv ℝ Γ x u t v) w + inner ℝ v (fderiv ℝ Γ x u t w) = 0 := by
  let L : (E →L[ℝ] (V →L[ℝ] V)) →L[ℝ] ℝ :=
    (skewPairing v w).comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) t)
  have h := annihilates_fderiv L Γ x u hd (by
    filter_upwards [hskew] with z hz
    exact (skewPairing_apply v w (Γ z t)).trans (hz t v w))
  exact (skewPairing_apply v w (fderiv ℝ Γ x u t)).symm.trans h

theorem curvature_skew (Γ : Form (E := E) (A := V →L[ℝ] V)) (x u t : E)
    (hd : DifferentiableAt ℝ Γ x)
    (hskew : ∀ᶠ z in 𝓝 x, ∀ t v w,
      inner ℝ (Γ z t v) w + inner ℝ v (Γ z t w) = 0) (v w : V) :
    inner ℝ (curvature Γ x u t v) w + inner ℝ v (curvature Γ x u t w) = 0 := by
  have h₁ := fderiv_form_skew Γ x u t hd hskew v w
  have h₂ := fderiv_form_skew Γ x t u hd hskew v w
  have h₃ := commutator_skew (Γ x u) (Γ x t)
    (Filter.Eventually.self_of_nhds hskew u) (Filter.Eventually.self_of_nhds hskew t) v w
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    inner_sub_left, inner_sub_right] at h₃
  simp only [curvature_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  linarith

end
end QuaternionicSymmetry.LocalConnection
