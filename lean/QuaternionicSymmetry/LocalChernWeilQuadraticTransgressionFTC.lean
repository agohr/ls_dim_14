import QuaternionicSymmetry.LocalChernWeilQuadraticFTC
import QuaternionicSymmetry.LocalChernWeilQuadraticTransgression

/-!
# The integrated local quadratic transgression derivative

This combines the actual pointwise exterior-derivative computation with the
Banach-valued path endpoint theorem.  The time integral here remains an
integral of four-forms.  Commuting `extDeriv` with a time integral of
three-forms, and passing to global de Rham classes, are separate steps. -/

namespace QuaternionicSymmetry.LocalChernWeilQuadraticTransgressionFTC

open QuaternionicSymmetry.LocalConnection QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilQuadraticFTC
  QuaternionicSymmetry.LocalChernWeilQuadraticTransgression
  QuaternionicSymmetry.LocalTraceSquareAlgebra

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedAddCommGroup (E [⋀^Fin 4]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 4]→L[ℝ] B) := inferInstance

/-- The endpoint difference is the path integral of the proved local
exterior derivative.  No endpoint equality or de Rham conclusion is assumed. -/
theorem traceSquareForm_sub_eq_integral_extDeriv
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    traceSquareForm T (Γ + θ) x - traceSquareForm T Γ x =
      ∫ t in (0 : ℝ)..1, (2 : ℝ) •
        extDeriv (traceConnectionCurvature T (Γ + t • θ) θ) x := by
  rw [traceSquareForm_path_integral_cyclic T hT Γ θ x
    (hΓ.differentiableAt (by norm_num))
    (hθ.differentiableAt (by norm_num))]
  congr 1
  funext t
  rw [extDeriv_traceConnectionCurvature T hT (Γ + t • θ) θ x
    (hΓ.add (hθ.const_smul t)) (hθ.differentiableAt (by norm_num))]

end
end QuaternionicSymmetry.LocalChernWeilQuadraticTransgressionFTC
