import QuaternionicSymmetry.LocalChernWeilQuadraticVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The endpoint of the quadratic local Chern--Weil path

The preceding variation module computes the derivative of `T(F∧F)` along
the affine connection path.  Here the Banach-valued fundamental theorem of
calculus integrates that derivative.  This is an equality of local four-forms
at a point; it makes no de Rham or global characteristic-class assertion. -/

namespace QuaternionicSymmetry.LocalChernWeilQuadraticFTC

open QuaternionicSymmetry.LocalConnection QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionVariation
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilQuadraticVariation
  QuaternionicSymmetry.LocalTraceSquareAlgebra

noncomputable section

/-- The Banach-valued endpoint theorem, stated without assuming the endpoint
equality.  Continuity of the displayed derivative supplies integrability. -/
theorem endpoint_sub_eq_integral {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f f' : ℝ → V) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') :
    f 1 - f 0 = ∫ t in (0 : ℝ)..1, f' t := by
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := f) (f' := f') (a := 0) (b := 1)
    (fun t _ => hf t) (hf'.intervalIntegrable 0 1)).symm

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 4]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 4]→L[ℝ] B) := inferInstance
local instance : NormedAddCommGroup
    ((E [⋀^Fin 2]→L[ℝ] R) →L[ℝ] E [⋀^Fin 4]→L[ℝ] B) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ
    ((E [⋀^Fin 2]→L[ℝ] R) →L[ℝ] E [⋀^Fin 4]→L[ℝ] B) :=
  ContinuousLinearMap.toNormedSpace

/-- The actual first-variation four-form at path time `t`. -/
def traceSquarePathIntegrand (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E) (t : ℝ) :
    E [⋀^Fin 4]→L[ℝ] B :=
  wedge22 (traceProduct T) (covariantDerivativeForm (Γ + t • θ) θ x)
    (curvatureForm (Γ + t • θ) x) +
  wedge22 (traceProduct T) (curvatureForm (Γ + t • θ) x)
    (covariantDerivativeForm (Γ + t • θ) θ x)

theorem continuous_traceSquarePathIntegrand (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) :
    Continuous (traceSquarePathIntegrand T Γ θ x) := by
  let F : ℝ → E [⋀^Fin 2]→L[ℝ] R :=
    fun t => curvatureForm (Γ + t • θ) x
  let D : ℝ → E [⋀^Fin 2]→L[ℝ] R :=
    fun t => covariantDerivativeForm (Γ + t • θ) θ x
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun t =>
    (curvatureForm_path_hasDerivAt Γ θ x hΓ hθ t).continuousAt
  have hscalar : Continuous (fun t : ℝ => 2 * t) :=
    continuous_const.mul continuous_id
  have hD : Continuous D := by
    have h : Continuous (fun t : ℝ =>
        covariantDerivativeForm Γ θ x + (2 * t) • wedgeSquareForm θ x) :=
      continuous_const.add (hscalar.smul continuous_const)
    simpa only [D, covariantDerivativeForm_path] using h
  let P := traceProduct T
  let W := wedge22CLM (E := E) (A := R) (B := R) (C := B) P
  have hW : Continuous (fun _ : ℝ => W) := continuous_const
  have hleft : Continuous (fun t => W (D t) (F t)) :=
    (hW.clm_apply hD).clm_apply hF
  have hright : Continuous (fun t => W (F t) (D t)) :=
    (hW.clm_apply hF).clm_apply hD
  simpa only [traceSquarePathIntegrand, W, P, F, D, wedge22CLM_apply]
    using hleft.add hright

/-- The actual endpoint difference of the local quadratic characteristic
form is the time integral of its proved first variation. -/
theorem traceSquareForm_path_integral [CompleteSpace B] (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) :
    traceSquareForm T (Γ + θ) x - traceSquareForm T Γ x =
      ∫ t in (0 : ℝ)..1, traceSquarePathIntegrand T Γ θ x t := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s => traceSquareForm T (Γ + s • θ) x)
        (traceSquarePathIntegrand T Γ θ x t) t := by
    intro t
    simpa only [traceSquarePathIntegrand] using
      traceSquareForm_path_hasDerivAt T Γ θ x hΓ hθ t
  have h := endpoint_sub_eq_integral
    (fun s : ℝ => traceSquareForm T (Γ + s • θ) x)
    (traceSquarePathIntegrand T Γ θ x) hderiv
    (continuous_traceSquarePathIntegrand T Γ θ x hΓ hθ)
  have hz : Γ + (0 : ℝ) • θ = Γ := by
    ext y v
    simp [Pi.smul_apply]
  have ho : Γ + (1 : ℝ) • θ = Γ + θ := by simp
  simpa only [hz, ho] using h

theorem traceSquarePathIntegrand_cyclic (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (x : E) (t : ℝ) :
    traceSquarePathIntegrand T Γ θ x t =
      (2 : ℝ) • wedge22 (traceProduct T)
        (covariantDerivativeForm (Γ + t • θ) θ x)
        (curvatureForm (Γ + t • θ) x) := by
  unfold traceSquarePathIntegrand
  rw [wedge22_cyclic (traceProduct T) (fun a b => hT a b)
    (curvatureForm (Γ + t • θ) x)
    (covariantDerivativeForm (Γ + t • θ) θ x)]
  module

/-- Cyclic trace puts the endpoint formula in the expected `2 T(Dθ∧F)`
form, still as an equality of local four-forms. -/
theorem traceSquareForm_path_integral_cyclic [CompleteSpace B]
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) :
    traceSquareForm T (Γ + θ) x - traceSquareForm T Γ x =
      ∫ t in (0 : ℝ)..1, (2 : ℝ) • wedge22 (traceProduct T)
        (covariantDerivativeForm (Γ + t • θ) θ x)
        (curvatureForm (Γ + t • θ) x) := by
  rw [traceSquareForm_path_integral T Γ θ x hΓ hθ]
  simp_rw [traceSquarePathIntegrand_cyclic T hT Γ θ x]

end
end QuaternionicSymmetry.LocalChernWeilQuadraticFTC
