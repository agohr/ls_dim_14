import QuaternionicSymmetry.LocalChernWeilOrderedTransgression

/-! Covariant derivative of the ordered primitive. -/

namespace QuaternionicSymmetry.LocalChernWeilOrderedTransgression

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalConnectionVariation
  QuaternionicSymmetry.LocalCovariantExterior
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilPowerVariation
  QuaternionicSymmetry.LocalContinuousWedgeCommutator
  QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.DifferentialFormCoefficient

noncomputable section

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The ordered first variation at a fixed connection. -/
def orderedCurvatureVariation (Γ θ : Form (E := E) (A := R)) (x : E) :
    (k : ℕ) → E [⋀^Fin (powerDegree k)]→L[ℝ] R
  | 0 => covariantDerivativeForm Γ θ x
  | k + 1 =>
      wedge (ContinuousLinearMap.mul ℝ R)
        (covariantDerivativeForm Γ θ x) (curvaturePowerForm Γ k x) +
      wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureForm Γ x) (orderedCurvatureVariation Γ θ x k)

theorem curvaturePowerPathVariation_eq_orderedCurvatureVariation
    (Γ θ : Form (E := E) (A := R)) (x : E) (t : ℝ) (k : ℕ) :
    curvaturePowerPathVariation Γ θ x t k =
      orderedCurvatureVariation (Γ + t • θ) θ x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [curvaturePowerPathVariation, orderedCurvatureVariation, ih]

private theorem covariantExteriorDerivative_connection_power
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    covariantExteriorDerivative Γ
      (fun y => wedge (ContinuousLinearMap.mul ℝ R)
        (connectionForm θ y) (curvaturePowerForm Γ k y)) x =
      degreeCast (show (1 + 1) + powerDegree k =
        (1 + powerDegree k) + 1 by omega)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (covariantDerivativeForm Γ θ x) (curvaturePowerForm Γ k x)) := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x
      (hθ.differentiableAt (by norm_num))
  rw [covariantExteriorDerivative_wedge_mul Γ
    (connectionForm θ) (curvaturePowerForm Γ k) x hθform
    (differentiableAt_curvaturePowerForm Γ x hΓ k)]
  rw [covariantExteriorDerivative_connectionForm Γ θ x
    (hθ.differentiableAt (by norm_num)),
    covariantExteriorDerivative_curvaturePowerForm_zero Γ x hΓ k]
  simp

private theorem covariantExteriorDerivative_curvature_ordered
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    covariantExteriorDerivative Γ
      (fun y => wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureForm Γ y) (orderedPrimitive Γ θ k y)) x =
      degreeCast (show 2 + (primitiveDegree k + 1) =
        (2 + primitiveDegree k) + 1 by omega)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (curvatureForm Γ x)
          (covariantExteriorDerivative Γ (orderedPrimitive Γ θ k) x)) := by
  have hΓ₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have hΓ₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF : DifferentiableAt ℝ (curvatureForm Γ) x :=
    differentiableAt_curvatureForm Γ x hΓ₁ hΓ₂
  rw [covariantExteriorDerivative_wedge_mul Γ
    (curvatureForm Γ) (orderedPrimitive Γ θ k) x hF
    (differentiableAt_orderedPrimitive Γ θ k x hΓ hθ)]
  rw [bianchi Γ x hΓ]
  simp

theorem covariantExteriorDerivative_orderedPrimitive
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    degreeCast (primitiveDegree_add_one k)
      (covariantExteriorDerivative Γ (orderedPrimitive Γ θ k) x) =
        orderedCurvatureVariation Γ θ x k := by
  induction k with
  | zero =>
      simpa [orderedPrimitive, orderedCurvatureVariation, degreeCast] using
        covariantExteriorDerivative_connectionForm Γ θ x
          (hθ.differentiableAt (by norm_num))
  | succ k ih =>
      let h₁ : 1 + powerDegree k = primitiveDegree (k + 1) := rfl
      let h₂ : 2 + primitiveDegree k = primitiveDegree (k + 1) :=
        primitiveDegree_succ_cast k
      let α : E → E [⋀^Fin (1 + powerDegree k)]→L[ℝ] R := fun y =>
        wedge (ContinuousLinearMap.mul ℝ R)
          (connectionForm θ y) (curvaturePowerForm Γ k y)
      let β : E → E [⋀^Fin (2 + primitiveDegree k)]→L[ℝ] R := fun y =>
        wedge (ContinuousLinearMap.mul ℝ R)
          (curvatureForm Γ y) (orderedPrimitive Γ θ k y)
      have hα : DifferentiableAt ℝ α x :=
        LocalChernWeilPowerTransgressionDerivative.differentiableAt_connectionCurvaturePowerForm
          Γ θ k x hΓ (hθ.differentiableAt (by norm_num))
      have hΓ₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
      have hΓ₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
        (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      have hF : DifferentiableAt ℝ (curvatureForm Γ) x :=
        differentiableAt_curvatureForm Γ x hΓ₁ hΓ₂
      have hβ : DifferentiableAt ℝ β x :=
        differentiableAt_wedge (ContinuousLinearMap.mul ℝ R)
          (curvatureForm Γ) (orderedPrimitive Γ θ k) x hF
          (differentiableAt_orderedPrimitive Γ θ k x hΓ hθ)
      have hsum : covariantExteriorDerivative Γ
          (orderedPrimitive Γ θ (k + 1)) x =
          covariantExteriorDerivative Γ (fun y => degreeCast h₁ (α y)) x +
          covariantExteriorDerivative Γ (fun y => degreeCast h₂ (β y)) x := by
        change covariantExteriorDerivative Γ
          ((fun y => degreeCast h₁ (α y)) +
            (fun y => degreeCast h₂ (β y))) x = _
        exact covariantExteriorDerivative_add Γ _ _ x
          (differentiableAt_degreeCast h₁ α x hα)
          (differentiableAt_degreeCast h₂ β x hβ)
      rw [hsum, covariantExteriorDerivative_degreeCast Γ h₁ α x,
        covariantExteriorDerivative_degreeCast Γ h₂ β x]
      have hαderiv := covariantExteriorDerivative_connection_power Γ θ k x hΓ hθ
      have hβderiv := covariantExteriorDerivative_curvature_ordered Γ θ k x hΓ hθ
      change covariantExteriorDerivative Γ α x = _ at hαderiv
      change covariantExteriorDerivative Γ β x = _ at hβderiv
      rw [hαderiv, hβderiv]
      simp only [degreeCast_add, degreeCast_trans, orderedCurvatureVariation]
      apply congrArg₂ (· + ·)
      · exact degreeCast_rfl (E := E) (R := R) _
      · rw [← degreeCast_wedge_right (primitiveDegree_add_one k)]
        rw [ih]

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Transport the output degree of a trace-valued alternating form. -/
def traceDegreeCast {m n : ℕ} (h : m = n)
    (ω : E [⋀^Fin m]→L[ℝ] B) : E [⋀^Fin n]→L[ℝ] B := by
  cases h
  exact ω

theorem traceDegreeCast_comp {m n : ℕ} (h : m = n)
    (T : R →L[ℝ] B) (ω : E [⋀^Fin m]→L[ℝ] R) :
    traceDegreeCast h (T.compContinuousAlternatingMap ω) =
      T.compContinuousAlternatingMap (degreeCast h ω) := by
  cases h
  rfl

/-- Cyclicity turns the covariant identity into an ordinary exterior derivative. -/
theorem extDeriv_traceOrderedPrimitive
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    traceDegreeCast (primitiveDegree_add_one k)
      (extDeriv (mapForm T (orderedPrimitive Γ θ k)) x) =
        T.compContinuousAlternatingMap (orderedCurvatureVariation Γ θ x k) := by
  have hcyc := cyclic_covariantExteriorDerivative T hT Γ
    (orderedPrimitive Γ θ k) x
    (differentiableAt_orderedPrimitive Γ θ k x hΓ hθ)
  rw [← hcyc]
  rw [traceDegreeCast_comp]
  rw [covariantExteriorDerivative_orderedPrimitive Γ θ k x hΓ hθ]

end
end QuaternionicSymmetry.LocalChernWeilOrderedTransgression
