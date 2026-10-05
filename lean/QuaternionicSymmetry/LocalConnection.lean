import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

/-! Local connection forms and curvature built from actual Fréchet
derivatives. The coefficient algebra is allowed to be noncommutative.
The formulas are continuous bilinear maps in the tangent arguments. -/

namespace QuaternionicSymmetry.LocalConnection

noncomputable section

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

abbrev Form := E → E →L[ℝ] A
abbrev Bilinear := E →L[ℝ] E →L[ℝ] A

def exteriorDerivative (Γ : Form (E := E) (A := A)) (x : E) : Bilinear (E := E) (A := A) :=
  fderiv ℝ Γ x - (fderiv ℝ Γ x).flip

def product (Γ θ : Form (E := E) (A := A)) (x : E) : Bilinear (E := E) (A := A) :=
  (ContinuousLinearMap.mul ℝ A).bilinearComp (Γ x) (θ x)

def wedgeSquare (Γ : Form (E := E) (A := A)) (x : E) : Bilinear (E := E) (A := A) :=
  product Γ Γ x - (product Γ Γ x).flip

def curvature (Γ : Form (E := E) (A := A)) (x : E) : Bilinear (E := E) (A := A) :=
  exteriorDerivative Γ x + wedgeSquare Γ x

def covariantDerivative (Γ θ : Form (E := E) (A := A)) (x : E) : Bilinear (E := E) (A := A) :=
  exteriorDerivative θ x + product Γ θ x - (product Γ θ x).flip +
    product θ Γ x - (product θ Γ x).flip

theorem exteriorDerivative_apply (Γ : Form (E := E) (A := A)) (x v w : E) :
    exteriorDerivative Γ x v w = fderiv ℝ Γ x v w - fderiv ℝ Γ x w v := rfl

theorem product_apply (Γ θ : Form (E := E) (A := A)) (x v w : E) :
    product Γ θ x v w = Γ x v * θ x w := rfl

theorem wedgeSquare_apply (Γ : Form (E := E) (A := A)) (x v w : E) :
    wedgeSquare Γ x v w = Γ x v * Γ x w - Γ x w * Γ x v := rfl

theorem curvature_apply (Γ : Form (E := E) (A := A)) (x v w : E) :
    curvature Γ x v w =
      fderiv ℝ Γ x v w - fderiv ℝ Γ x w v + Γ x v * Γ x w - Γ x w * Γ x v := by
  simp only [curvature, ContinuousLinearMap.add_apply, exteriorDerivative_apply, wedgeSquare_apply]
  abel

theorem covariantDerivative_apply (Γ θ : Form (E := E) (A := A)) (x v w : E) :
    covariantDerivative Γ θ x v w =
      fderiv ℝ θ x v w - fderiv ℝ θ x w v + Γ x v * θ x w - Γ x w * θ x v +
        θ x v * Γ x w - θ x w * Γ x v := rfl

theorem curvature_self (Γ : Form (E := E) (A := A)) (x v : E) : curvature Γ x v v = 0 := by
  simp [curvature_apply]

theorem curvature_antisymm (Γ : Form (E := E) (A := A)) (x v w : E) :
    curvature Γ x v w = -curvature Γ x w v := by
  simp only [curvature_apply]
  abel

theorem exteriorDerivative_add (Γ θ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) :
    exteriorDerivative (Γ + θ) x = exteriorDerivative Γ x + exteriorDerivative θ x := by
  ext v w
  simp only [exteriorDerivative_apply, fderiv_add hΓ hθ, ContinuousLinearMap.add_apply]
  abel

theorem curvature_add (Γ θ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) :
    curvature (Γ + θ) x = curvature Γ x + covariantDerivative Γ θ x + wedgeSquare θ x := by
  ext v w
  simp only [ContinuousLinearMap.add_apply, curvature_apply, covariantDerivative_apply,
    wedgeSquare_apply, fderiv_add hΓ hθ, Pi.add_apply]
  noncomm_ring

theorem curvature_path (Γ θ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) (t : ℝ) :
    curvature (Γ + t • θ) x = curvature Γ x + t • covariantDerivative Γ θ x +
      t ^ 2 • wedgeSquare θ x := by
  rw [curvature_add Γ (t • θ) x hΓ (hθ.const_smul t)]
  ext v w
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    covariantDerivative_apply, wedgeSquare_apply, fderiv_const_smul hθ,
    Pi.smul_apply, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

/-- Cancellation of the compact model term once the torsion equation and
the split-curvature identity have been established for actual local forms. -/
theorem curvature_add_of_torsion_free (Γ θ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x)
    (W : Bilinear (E := E) (A := A))
    (hT : covariantDerivative Γ θ x = 0)
    (hR : curvature Γ x = -wedgeSquare θ x + W) : curvature (Γ + θ) x = W := by
  rw [curvature_add Γ θ x hΓ hθ, hT, hR]
  abel

end
end QuaternionicSymmetry.LocalConnection
