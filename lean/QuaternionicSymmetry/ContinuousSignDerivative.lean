import QuaternionicSymmetry.ContinuousSignRigidity
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Adjoint
import QuaternionicSymmetry.LocalConnectionGauge

/-! The logarithmic derivative of an orthogonal gauge is insensitive to a
locally constant central sign. -/
namespace QuaternionicSymmetry.ContinuousSignDerivative
open scoped Topology
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem fderiv_mul_adjoint_eq_of_eventually_sign
    (f g : E → (V →L[ℝ] V)) (x u : E)
    (h : f =ᶠ[𝓝 x] g ∨ f =ᶠ[𝓝 x] (fun y => -g y)) :
    fderiv ℝ f x u * (f x).adjoint =
      fderiv ℝ g x u * (g x).adjoint := by
  rcases h with h | h
  · rw [h.fderiv_eq, h.self_of_nhds]
  · have hd : fderiv ℝ f x = -fderiv ℝ g x := by
      rw [h.fderiv_eq]
      exact fderiv_neg
    rw [hd, h.self_of_nhds]
    simp

theorem fderiv_mul_adjoint_eq_of_sign
    (f g : E → (V →L[ℝ] V)) (x u : E)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hx : g x ≠ 0)
    (hsign : ∀ᶠ y in 𝓝 x, f y = g y ∨ f y = -g y) :
    fderiv ℝ f x u * (f x).adjoint =
      fderiv ℝ g x u * (g x).adjoint :=
  fderiv_mul_adjoint_eq_of_eventually_sign f g x u
    (ContinuousSignRigidity.eventually_eq_or_neg f g x hf hg hx hsign)

theorem adjoint_mul_fderiv_eq_of_eventually_sign
    (f g : E → (V →L[ℝ] V)) (x u : E)
    (h : f =ᶠ[𝓝 x] g ∨ f =ᶠ[𝓝 x] (fun y => -g y)) :
    (f x).adjoint * fderiv ℝ f x u =
      (g x).adjoint * fderiv ℝ g x u := by
  rcases h with h | h
  · rw [h.fderiv_eq, h.self_of_nhds]
  · have hd : fderiv ℝ f x = -fderiv ℝ g x := by
      rw [h.fderiv_eq]
      exact fderiv_neg
    rw [hd, h.self_of_nhds]
    simp

theorem transform_eq_of_eventually_sign
    (Γ : LocalConnection.Form (E := E) (A := V →L[ℝ] V))
    (f g : E → (V →L[ℝ] V)) (x u : E)
    (h : f =ᶠ[𝓝 x] g ∨ f =ᶠ[𝓝 x] (fun y => -g y)) :
    LocalConnectionGauge.transform Γ f (fun y => (f y).adjoint) x u =
      LocalConnectionGauge.transform Γ g (fun y => (g y).adjoint) x u := by
  rcases h with h | h
  · simp only [LocalConnectionGauge.transform_apply, h.fderiv_eq, h.self_of_nhds]
  · have hd : fderiv ℝ f x = -fderiv ℝ g x := by
      rw [h.fderiv_eq]
      exact fderiv_neg
    simp only [LocalConnectionGauge.transform_apply, hd, h.self_of_nhds]
    simp [mul_add]

end QuaternionicSymmetry.ContinuousSignDerivative
