import QuaternionicSymmetry.LocalChernWeilPowerTransgressionDerivative

/-!
# Ordered local Chern--Simons primitive in every positive degree

The recursively ordered primitive begins with the path direction one-form
`θ` and inserts `θ` into every curvature word. Its covariant exterior
derivative is the complete ordered curvature variation, even when coefficient
multiplication is noncommutative. A cyclic trace then turns the covariant
identity into an ordinary exterior transgression.
-/

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
  QuaternionicSymmetry.ContinuousWedgeShuffle

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- Degree of the primitive for `F^(k+1)`. -/
def primitiveDegree : ℕ → ℕ
  | 0 => 1
  | k + 1 => 1 + powerDegree k

theorem primitiveDegree_add_one (k : ℕ) :
    primitiveDegree k + 1 = powerDegree k := by
  cases k with
  | zero => rfl
  | succ k =>
      simp only [primitiveDegree, powerDegree]
      omega

theorem primitiveDegree_succ_cast (k : ℕ) :
    2 + primitiveDegree k = primitiveDegree (k + 1) := by
  rw [primitiveDegree, ← primitiveDegree_add_one k]
  omega

/-- Transport of a continuous alternating form along equality of degrees. -/
def degreeCast {m n : ℕ} (h : m = n)
    (ω : E [⋀^Fin m]→L[ℝ] R) :
    E [⋀^Fin n]→L[ℝ] R := by
  cases h
  exact ω

@[simp] theorem degreeCast_apply {m n : ℕ} (h : m = n)
    (ω : E [⋀^Fin m]→L[ℝ] R) (v : Fin n → E) :
    degreeCast h ω v = ω (v ∘ finCongr h) := by
  cases h
  rfl

@[simp] theorem degreeCast_rfl {m : ℕ}
    (ω : E [⋀^Fin m]→L[ℝ] R) :
    degreeCast (E := E) (R := R) rfl ω = ω := rfl

theorem differentiableAt_degreeCast {m n : ℕ} (h : m = n)
    (ω : E → E [⋀^Fin m]→L[ℝ] R) (x : E)
    (hω : DifferentiableAt ℝ ω x) :
    DifferentiableAt ℝ (fun y => degreeCast h (ω y)) x := by
  cases h
  exact hω

@[simp] theorem degreeCast_add {m n : ℕ} (h : m = n)
    (ω η : E [⋀^Fin m]→L[ℝ] R) :
    degreeCast h (ω + η) = degreeCast h ω + degreeCast h η := by
  cases h
  rfl

@[simp] theorem degreeCast_zero {m n : ℕ} (h : m = n) :
    degreeCast (E := E) (R := R) h 0 = 0 := by
  cases h
  rfl

@[simp] theorem degreeCast_zsmul {m n : ℕ} (h : m = n)
    (z : ℤ) (ω : E [⋀^Fin m]→L[ℝ] R) :
    degreeCast h (z • ω) = z • degreeCast h ω := by
  cases h
  rfl

@[simp] theorem degreeCast_trans {m n l : ℕ} (h : m = n) (g : n = l)
    (ω : E [⋀^Fin m]→L[ℝ] R) :
    degreeCast g (degreeCast h ω) = degreeCast (h.trans g) ω := by
  cases h
  cases g
  rfl

theorem degreeCast_wedge_left {p p' q : ℕ} (h : p = p')
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    wedge (ContinuousLinearMap.mul ℝ R) (degreeCast h α) β =
      degreeCast (congrArg (· + q) h)
        (wedge (ContinuousLinearMap.mul ℝ R) α β) := by
  cases h
  rfl

theorem degreeCast_wedge_right {p q q' : ℕ} (h : q = q')
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    wedge (ContinuousLinearMap.mul ℝ R) α (degreeCast h β) =
      degreeCast (congrArg (p + ·) h)
        (wedge (ContinuousLinearMap.mul ℝ R) α β) := by
  cases h
  rfl

theorem covariantExteriorDerivative_degreeCast {m n : ℕ}
    (Γ : Form (E := E) (A := R)) (h : m = n)
    (ω : E → E [⋀^Fin m]→L[ℝ] R) (x : E) :
    covariantExteriorDerivative Γ (fun y => degreeCast h (ω y)) x =
      degreeCast (congrArg (· + 1) h)
        (covariantExteriorDerivative Γ ω x) := by
  cases h
  rfl

theorem covariantExteriorDerivative_add
    {m : ℕ} (Γ : Form (E := E) (A := R))
    (ω η : E → E [⋀^Fin m]→L[ℝ] R) (x : E)
    (hω : DifferentiableAt ℝ ω x) (hη : DifferentiableAt ℝ η x) :
    covariantExteriorDerivative Γ (ω + η) x =
      covariantExteriorDerivative Γ ω x +
        covariantExteriorDerivative Γ η x := by
  have hc : commutator Γ (ω x + η x) x =
      commutator Γ (ω x) x + commutator Γ (η x) x := by
    ext v
    simp only [commutator_apply, ContinuousAlternatingMap.add_apply,
      add_mul, mul_add, ← Finset.sum_add_distrib, ← smul_add]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    abel
  simp only [covariantExteriorDerivative, Pi.add_apply, extDeriv_add hω hη, hc]
  abel

theorem covariantExteriorDerivative_wedge_mul {p q : ℕ}
    (Γ : Form (E := E) (A := R))
    (α : E → E [⋀^Fin p]→L[ℝ] R)
    (β : E → E [⋀^Fin q]→L[ℝ] R) (x : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    covariantExteriorDerivative Γ
        (fun y => wedge (ContinuousLinearMap.mul ℝ R) (α y) (β y)) x =
      degreeCast (show (p + 1) + q = (p + q) + 1 by omega)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (covariantExteriorDerivative Γ α x) (β x)) +
      (-1 : ℤ) ^ p • degreeCast
        (show p + (q + 1) = (p + q) + 1 by omega)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (α x) (covariantExteriorDerivative Γ β x)) := by
  ext v
  rw [covariantExteriorDerivative_wedge_mul_apply Γ α β x hα hβ v]
  simp only [ContinuousAlternatingMap.add_apply, degreeCast_apply]
  congr 1

/-- The ordered primitive: `S₀=θ` and
`S₍k+1₎=θ∧F^(k+1)+F∧S_k`. -/
def orderedPrimitive (Γ θ : Form (E := E) (A := R)) :
    (k : ℕ) → E → E [⋀^Fin (primitiveDegree k)]→L[ℝ] R
  | 0 => connectionForm θ
  | k + 1 => fun x =>
      degreeCast (show 1 + powerDegree k = primitiveDegree (k + 1) by rfl)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (connectionForm θ x) (curvaturePowerForm Γ k x)) +
      degreeCast (primitiveDegree_succ_cast k)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (curvatureForm Γ x) (orderedPrimitive Γ θ k x))

theorem differentiableAt_orderedPrimitive
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    DifferentiableAt ℝ (orderedPrimitive Γ θ k) x := by
  have hθ₁ : DifferentiableAt ℝ θ x := hθ.differentiableAt (by norm_num)
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x hθ₁
  have hΓ₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have hΓ₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF : DifferentiableAt ℝ (curvatureForm Γ) x :=
    differentiableAt_curvatureForm Γ x hΓ₁ hΓ₂
  induction k with
  | zero => exact hθform
  | succ k ih =>
      exact (differentiableAt_degreeCast
        (show 1 + powerDegree k = primitiveDegree (k + 1) by rfl)
        (fun y => wedge (ContinuousLinearMap.mul ℝ R)
          (connectionForm θ y) (curvaturePowerForm Γ k y)) x
        (differentiableAt_wedge (ContinuousLinearMap.mul ℝ R)
          (connectionForm θ) (curvaturePowerForm Γ k) x hθform
          (differentiableAt_curvaturePowerForm Γ x hΓ k))).add
        (differentiableAt_degreeCast (primitiveDegree_succ_cast k)
          (fun y => wedge (ContinuousLinearMap.mul ℝ R)
            (curvatureForm Γ y) (orderedPrimitive Γ θ k y)) x
          (differentiableAt_wedge (ContinuousLinearMap.mul ℝ R)
            (curvatureForm Γ) (orderedPrimitive Γ θ k) x hF ih))

end
end QuaternionicSymmetry.LocalChernWeilOrderedTransgression
