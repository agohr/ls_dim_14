import QuaternionicSymmetry.LocalConnectionForms
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! The first variation of curvature along an affine path of local
connections, as an actual derivative valued in alternating two-forms. -/

namespace QuaternionicSymmetry.LocalConnectionVariation

open LocalConnection LocalConnectionForms

noncomputable section

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

theorem covariantDerivativeForm_path (Γ θ : Form (E := E) (A := A)) (x : E) (t : ℝ) :
    covariantDerivativeForm (Γ + t • θ) θ x =
      covariantDerivativeForm Γ θ x + (2 * t) • wedgeSquareForm θ x := by
  ext v
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    covariantDerivativeForm_apply, wedgeSquareForm_apply, covariantDerivative_apply,
    wedgeSquare_apply, Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  module

theorem curvatureForm_path_hasDerivAt (Γ θ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) (t : ℝ) :
    HasDerivAt (fun s : ℝ => curvatureForm (Γ + s • θ) x)
      (covariantDerivativeForm (Γ + t • θ) θ x) t := by
  have he : (fun s : ℝ => curvatureForm (Γ + s • θ) x) =
      fun s => curvatureForm Γ x + s • covariantDerivativeForm Γ θ x +
        s ^ 2 • wedgeSquareForm θ x := by
    funext s
    exact curvatureForm_path Γ θ x hΓ hθ s
  rw [he, covariantDerivativeForm_path]
  have hd := ((hasDerivAt_const t (curvatureForm Γ x)).add
    ((hasDerivAt_id t).smul_const (covariantDerivativeForm Γ θ x))).add
      ((hasDerivAt_pow 2 t).smul_const (wedgeSquareForm θ x))
  simpa using hd

theorem curvatureForm_path_deriv (Γ θ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) (t : ℝ) :
    deriv (fun s : ℝ => curvatureForm (Γ + s • θ) x) t =
      covariantDerivativeForm (Γ + t • θ) θ x :=
  (curvatureForm_path_hasDerivAt Γ θ x hΓ hθ t).deriv

end
end QuaternionicSymmetry.LocalConnectionVariation
