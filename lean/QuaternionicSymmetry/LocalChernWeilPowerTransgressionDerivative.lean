import QuaternionicSymmetry.LocalChernWeilPowerPolynomial
import QuaternionicSymmetry.LocalContinuousWedgeCommutator

/-!
# Exterior derivative of the local Chern--Simons integrand

The covariant graded Leibniz rule and Bianchi identity identify the exterior
derivative of `T(θ ∧ F^(k+1))` with the normalized wedge
`T(D_Γ θ ∧ F^(k+1))`.  This is an actual equality of continuous alternating
forms at a point.  Cyclicity of `T` removes the connection commutator.
-/

namespace QuaternionicSymmetry.LocalChernWeilPowerTransgressionDerivative

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalCovariantExterior
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilPowerTransgressionForm
  QuaternionicSymmetry.LocalChernWeilCubicCyclicity
  QuaternionicSymmetry.LocalContinuousWedgeCommutator
  QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeShuffle
  QuaternionicSymmetry.DifferentialFormCoefficient

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The ordered algebra-valued primitive before applying the trace. -/
def connectionCurvaturePowerForm
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) :
    E → E [⋀^Fin (1 + powerDegree k)]→L[ℝ] R := fun x =>
  wedge (ContinuousLinearMap.mul ℝ R)
    (connectionForm θ x) (curvaturePowerForm Γ k x)

theorem differentiableAt_connectionCurvaturePowerForm
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x) :
    DifferentiableAt ℝ (connectionCurvaturePowerForm Γ θ k) x := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x hθ
  exact differentiableAt_wedge (ContinuousLinearMap.mul ℝ R)
    (connectionForm θ) (curvaturePowerForm Γ k) x
    hθform (differentiableAt_curvaturePowerForm Γ x hΓ k)

theorem traceConnectionCurvaturePower_eq_mapForm
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R)) (k : ℕ) :
    traceConnectionCurvaturePower T Γ θ k =
      mapForm T (connectionCurvaturePowerForm Γ θ k) := by
  funext x
  exact trace_wedge_eq_map T (connectionForm θ x)
    (curvaturePowerForm Γ k x)

/-- Covariant differentiation of the algebra-valued primitive leaves only
the derivative of the path direction: all curvature-power terms vanish by
the all-degree Bianchi identity. -/
theorem covariantExteriorDerivative_connectionCurvaturePowerForm_apply
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x)
    (v : Fin (1 + powerDegree k + 1) → E) :
    covariantExteriorDerivative Γ (connectionCurvaturePowerForm Γ θ k) x v =
      wedge (ContinuousLinearMap.mul ℝ R)
        (covariantDerivativeForm Γ θ x)
        (curvaturePowerForm Γ k x)
          (v ∘ wedgeLeftIndex 1 (powerDegree k)) := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x hθ
  have h := covariantExteriorDerivative_wedge_mul_apply
    (p := 1) (q := powerDegree k) Γ
    (connectionForm θ) (curvaturePowerForm Γ k)
    x hθform (differentiableAt_curvaturePowerForm Γ x hΓ k) v
  change covariantExteriorDerivative Γ
      (fun y => wedge (ContinuousLinearMap.mul ℝ R)
        (connectionForm θ y) (curvaturePowerForm Γ k y)) x v = _ at h
  rw [covariantExteriorDerivative_connectionForm Γ θ x hθ,
    covariantExteriorDerivative_curvaturePowerForm_zero Γ x hΓ k] at h
  simpa [connectionCurvaturePowerForm] using h

/-- For a cyclic trace, the actual exterior derivative of the normalized
local Chern--Simons form is the trace of `D_Γθ∧F^(k+1)`. -/
theorem extDeriv_traceConnectionCurvaturePower_apply
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x)
    (v : Fin (1 + powerDegree k + 1) → E) :
    extDeriv (traceConnectionCurvaturePower T Γ θ k) x v =
      wedge (traceProduct T)
        (covariantDerivativeForm Γ θ x)
        (curvaturePowerForm Γ k x)
          (v ∘ wedgeLeftIndex 1 (powerDegree k)) := by
  rw [traceConnectionCurvaturePower_eq_mapForm]
  have hcyc := cyclic_covariantExteriorDerivative T hT Γ
    (connectionCurvaturePowerForm Γ θ k) x
    (differentiableAt_connectionCurvaturePowerForm Γ θ k x hΓ hθ)
  rw [← hcyc]
  change T (covariantExteriorDerivative Γ
    (connectionCurvaturePowerForm Γ θ k) x v) = _
  rw [covariantExteriorDerivative_connectionCurvaturePowerForm_apply
    Γ θ k x hΓ hθ v]
  rw [trace_wedge_eq_map]
  rfl

end
end QuaternionicSymmetry.LocalChernWeilPowerTransgressionDerivative
