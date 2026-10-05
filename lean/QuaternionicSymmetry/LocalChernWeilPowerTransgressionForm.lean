import QuaternionicSymmetry.LocalChernWeilPowerVariation
import QuaternionicSymmetry.LocalChernWeilCubicCyclicity
import QuaternionicSymmetry.ContinuousWedgeLeibniz

/-!
# Local Chern--Simons integrands in every positive curvature degree

For the ordered curvature power `F^(k+1)`, this constructs the normalized
`(2k+3)`-form `T(θ ∧ F^(k+1))`. It uses actual continuous alternating maps,
and differentiability is proved at a point from local C² regularity of the
connection and first differentiability of the path direction.
-/

namespace QuaternionicSymmetry.LocalChernWeilPowerTransgressionForm

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilQuadraticTransgression
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilCubicTransgression
  QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeShuffle

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The normalized ordered `T(θ ∧ F^(k+1))` form. -/
def traceConnectionCurvaturePower (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) :
    E → E [⋀^Fin (1 + powerDegree k)]→L[ℝ] B := fun x =>
  wedge (traceProduct T)
    (connectionForm θ x) (curvaturePowerForm Γ k x)

/-- The quadratic three-form is the first case of the all-degree construction. -/
theorem traceConnectionCurvaturePower_zero (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) :
    traceConnectionCurvaturePower T Γ θ 0 =
      traceConnectionCurvature T Γ θ := by
  rfl

/-- The cubic five-form is the second case of the all-degree construction. -/
theorem traceConnectionCurvaturePower_one (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) :
    traceConnectionCurvaturePower T Γ θ 1 =
      traceConnectionCurvatureSquare T Γ θ := by
  rfl

theorem differentiableAt_traceConnectionCurvaturePower
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R))
    (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x) :
    DifferentiableAt ℝ (traceConnectionCurvaturePower T Γ θ k) x := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x hθ
  exact differentiableAt_wedge (p := 1) (q := powerDegree k)
    (traceProduct T) (connectionForm θ)
    (curvaturePowerForm Γ k) x hθform
    (differentiableAt_curvaturePowerForm Γ x hΓ k)

/-- The exterior derivative is the alternating sum of the two actual
Fréchet slot derivatives; the graded Chern--Weil identity is a later step. -/
theorem extDeriv_traceConnectionCurvaturePower_apply
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R))
    (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x)
    (v : Fin (1 + powerDegree k + 1) → E) :
    extDeriv (traceConnectionCurvaturePower T Γ θ k) x v =
      ∑ i : Fin (1 + powerDegree k + 1), (-1 : ℤ) ^ i.val •
        (wedge (traceProduct T)
            (fderiv ℝ (connectionForm θ) x (v i))
            (curvaturePowerForm Γ k x) (i.removeNth v) +
          wedge (traceProduct T)
            (connectionForm θ x)
            (fderiv ℝ (curvaturePowerForm Γ k) x (v i))
              (i.removeNth v)) := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x hθ
  have h := extDeriv_wedge_apply (p := 1) (q := powerDegree k)
    (traceProduct T) (connectionForm θ) (curvaturePowerForm Γ k)
    x hθform (differentiableAt_curvaturePowerForm Γ x hΓ k) v
  simpa only [traceConnectionCurvaturePower] using h

/-- The graded exterior Leibniz rule for every normalized local Chern--Simons
integrand, with the explicit reassociation of the left vector block. -/
theorem extDeriv_traceConnectionCurvaturePower_leibniz_apply
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R))
    (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x)
    (v : Fin (1 + powerDegree k + 1) → E) :
    extDeriv (traceConnectionCurvaturePower T Γ θ k) x v =
      wedge (traceProduct T)
        (extDeriv (connectionForm θ) x)
        (curvaturePowerForm Γ k x)
          (v ∘ wedgeLeftIndex 1 (powerDegree k)) +
      (-1 : ℤ) ^ (1 : ℕ) •
        wedge (traceProduct T)
          (connectionForm θ x)
          (extDeriv (curvaturePowerForm Γ k) x) v := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x hθ
  have h := ContinuousWedgeLeibniz.extDeriv_wedge_apply
    (p := 1) (q := powerDegree k)
    (traceProduct T) (connectionForm θ) (curvaturePowerForm Γ k)
    x hθform (differentiableAt_curvaturePowerForm Γ x hΓ k) v
  simpa only [traceConnectionCurvaturePower] using h

end
end QuaternionicSymmetry.LocalChernWeilPowerTransgressionForm
