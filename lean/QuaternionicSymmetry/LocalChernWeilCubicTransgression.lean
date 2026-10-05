import QuaternionicSymmetry.LocalChernWeilCubicVariation
import QuaternionicSymmetry.ContinuousWedge

/-!
# The local cubic Chern--Simons five-form

This file constructs the normalized five-form `T(θ ∧ F ∧ F)` using actual
continuous alternating maps. Its spatial differentiability and exterior
derivative are computed from Fréchet derivatives. Identifying that derivative
with the cubic first variation requires the graded wedge Leibniz and cyclic
trace identities, and is not asserted here.
-/

namespace QuaternionicSymmetry.LocalChernWeilCubicTransgression

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilCubicForm
  QuaternionicSymmetry.ContinuousWedge

noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedAddCommGroup (E [⋀^Fin 1]→L[ℝ] R) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 1]→L[ℝ] R) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 4]→L[ℝ] R) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 4]→L[ℝ] R) := inferInstance

/-- The normalized five-form `T(θ∧F_Γ∧F_Γ)`. -/
def traceConnectionCurvatureSquare (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) :
    E → E [⋀^Fin 5]→L[ℝ] B := fun x =>
  wedge (p := 1) (q := 4) (traceProduct T)
    (connectionForm θ x)
    (wedge22 (ContinuousLinearMap.mul ℝ R)
      (curvatureForm Γ x) (curvatureForm Γ x))

/-- Only local `C²` regularity of the connection and first differentiability
of the path direction are needed for this spatial derivative. -/
theorem differentiableAt_traceConnectionCurvatureSquare (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x) :
    DifferentiableAt ℝ (traceConnectionCurvatureSquare T Γ θ) x := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x hθ
  have hΓ₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have hΓ₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF : DifferentiableAt ℝ (curvatureForm Γ) x :=
    differentiableAt_curvatureForm Γ x hΓ₁ hΓ₂
  exact differentiableAt_wedge (p := 1) (q := 4)
    (traceProduct T)
    (connectionForm θ)
    (fun y => wedge22 (ContinuousLinearMap.mul ℝ R)
      (curvatureForm Γ y) (curvatureForm Γ y))
    x hθform
    (differentiableAt_wedge22 (ContinuousLinearMap.mul ℝ R)
      (curvatureForm Γ) (curvatureForm Γ) x hF hF)

/-- The exterior derivative of the concrete five-form, expressed as the
six-term alternating sum of actual Fréchet slot derivatives. -/
theorem extDeriv_traceConnectionCurvatureSquare_apply (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x)
    (v : Fin 6 → E) :
    extDeriv (traceConnectionCurvatureSquare T Γ θ) x v =
      ∑ i : Fin 6, (-1 : ℤ) ^ i.val •
        (wedge (p := 1) (q := 4) (traceProduct T)
            (fderiv ℝ (connectionForm θ) x (v i))
            (wedge22 (ContinuousLinearMap.mul ℝ R)
              (curvatureForm Γ x) (curvatureForm Γ x)) (i.removeNth v) +
          wedge (p := 1) (q := 4) (traceProduct T)
            (connectionForm θ x)
            (fderiv ℝ (fun y => wedge22 (ContinuousLinearMap.mul ℝ R)
              (curvatureForm Γ y) (curvatureForm Γ y)) x (v i))
              (i.removeNth v)) := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x hθ
  have hΓ₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have hΓ₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF : DifferentiableAt ℝ (curvatureForm Γ) x :=
    differentiableAt_curvatureForm Γ x hΓ₁ hΓ₂
  have h := extDeriv_wedge_apply (p := 1) (q := 4) (traceProduct T)
    (connectionForm θ)
    (fun y => wedge22 (ContinuousLinearMap.mul ℝ R)
      (curvatureForm Γ y) (curvatureForm Γ y))
    x hθform
    (differentiableAt_wedge22 (ContinuousLinearMap.mul ℝ R)
      (curvatureForm Γ) (curvatureForm Γ) x hF hF) v
  simpa only [traceConnectionCurvatureSquare] using h

end
end QuaternionicSymmetry.LocalChernWeilCubicTransgression
