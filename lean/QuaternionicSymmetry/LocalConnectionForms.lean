import QuaternionicSymmetry.LocalConnection
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-! Local connection curvature as a genuine continuous alternating two-form,
with its derivative term identified with mathlib's exterior derivative. -/

namespace QuaternionicSymmetry.LocalConnectionForms

open LocalConnection ContinuousAlternatingMap

noncomputable section

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

def oneFormMap : (E →L[ℝ] A) →L[ℝ] E [⋀^Fin 1]→L[ℝ] A :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := A)
    (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap

theorem oneFormMap_apply (f : E →L[ℝ] A) (v : Fin 1 → E) : oneFormMap f v = f (v 0) := rfl

def alternatingPart (B : Bilinear (E := E) (A := A)) : E [⋀^Fin 2]→L[ℝ] A :=
  ContinuousAlternatingMap.alternatizeUncurryFin (oneFormMap.comp B)

theorem alternatingPart_apply (B : Bilinear (E := E) (A := A)) (v : Fin 2 → E) :
    alternatingPart B v = B (v 0) (v 1) - B (v 1) (v 0) := by
  simp [alternatingPart, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_two, oneFormMap_apply, Fin.removeNth, sub_eq_add_neg]

def connectionForm (Γ : Form (E := E) (A := A)) : E → E [⋀^Fin 1]→L[ℝ] A :=
  fun x => oneFormMap (Γ x)

def wedgeSquareForm (Γ : Form (E := E) (A := A)) (x : E) : E [⋀^Fin 2]→L[ℝ] A :=
  alternatingPart (product Γ Γ x)

def curvatureForm (Γ : Form (E := E) (A := A)) (x : E) : E [⋀^Fin 2]→L[ℝ] A :=
  alternatingPart (fderiv ℝ Γ x + product Γ Γ x)

def covariantDerivativeForm (Γ θ : Form (E := E) (A := A)) (x : E) : E [⋀^Fin 2]→L[ℝ] A :=
  alternatingPart (fderiv ℝ θ x + product Γ θ x + product θ Γ x)

theorem wedgeSquareForm_apply (Γ : Form (E := E) (A := A)) (x : E) (v : Fin 2 → E) :
    wedgeSquareForm Γ x v = wedgeSquare Γ x (v 0) (v 1) := by
  rw [wedgeSquareForm, alternatingPart_apply, product_apply, product_apply, wedgeSquare_apply]

theorem curvatureForm_apply (Γ : Form (E := E) (A := A)) (x : E) (v : Fin 2 → E) :
    curvatureForm Γ x v = curvature Γ x (v 0) (v 1) := by
  simp only [curvatureForm, alternatingPart_apply, ContinuousLinearMap.add_apply,
    product_apply, curvature_apply]
  abel

theorem covariantDerivativeForm_apply (Γ θ : Form (E := E) (A := A)) (x : E) (v : Fin 2 → E) :
    covariantDerivativeForm Γ θ x v = covariantDerivative Γ θ x (v 0) (v 1) := by
  simp only [covariantDerivativeForm, alternatingPart_apply, ContinuousLinearMap.add_apply,
    product_apply, covariantDerivative_apply]
  abel

theorem extDeriv_connectionForm (Γ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) :
    extDeriv (connectionForm Γ) x = alternatingPart (fderiv ℝ Γ x) := by
  have hd := ((oneFormMap (E := E) (A := A)).hasFDerivAt.comp x hΓ.hasFDerivAt).fderiv
  change fderiv ℝ (connectionForm Γ) x = oneFormMap.comp (fderiv ℝ Γ x) at hd
  rw [extDeriv, hd]
  rfl

theorem curvatureForm_eq_extDeriv_add (Γ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) :
    curvatureForm Γ x = extDeriv (connectionForm Γ) x + wedgeSquareForm Γ x := by
  rw [extDeriv_connectionForm Γ x hΓ]
  ext v
  simp only [curvatureForm, wedgeSquareForm, ContinuousAlternatingMap.add_apply,
    alternatingPart_apply, ContinuousLinearMap.add_apply]
  abel

theorem curvatureForm_path (Γ θ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) (t : ℝ) :
    curvatureForm (Γ + t • θ) x = curvatureForm Γ x + t • covariantDerivativeForm Γ θ x +
      t ^ 2 • wedgeSquareForm θ x := by
  ext v
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    curvatureForm_apply, covariantDerivativeForm_apply, wedgeSquareForm_apply]
  have h := congrArg (fun B : Bilinear (E := E) (A := A) => B (v 0) (v 1))
    (curvature_path Γ θ x hΓ hθ t)
  exact h

end
end QuaternionicSymmetry.LocalConnectionForms
