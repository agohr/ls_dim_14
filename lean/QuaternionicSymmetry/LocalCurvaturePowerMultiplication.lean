import QuaternionicSymmetry.LocalChernWeilOrderedTransgression
import QuaternionicSymmetry.ContinuousWedgeAssocComparison

/-! Associative multiplication of the ordered normalized curvature wedge powers. -/

namespace QuaternionicSymmetry.LocalCurvaturePowerMultiplication

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeAssocComparison

noncomputable section

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- Recursive index for a product of two positive curvature powers. -/
def concatIndex : ℕ → ℕ → ℕ
  | 0, j => j + 1
  | i + 1, j => concatIndex i j + 1

theorem concatIndex_eq (i j : ℕ) : concatIndex i j = i + j + 1 := by
  induction i with
  | zero => simp [concatIndex]
  | succ i ih => simp only [concatIndex, ih]; omega

theorem powerDegree_concat (i j : ℕ) :
    powerDegree i + powerDegree j = powerDegree (concatIndex i j) := by
  rw [concatIndex_eq]
  simp only [powerDegree_eq]
  omega

private theorem wedge_mul_assoc_cast {p q r : ℕ}
    (α : E [⋀^Fin p]→L[ℝ] R)
    (β : E [⋀^Fin q]→L[ℝ] R)
    (γ : E [⋀^Fin r]→L[ℝ] R) :
    degreeCast (Nat.add_assoc p q r)
      (wedge (ContinuousLinearMap.mul ℝ R)
        (wedge (ContinuousLinearMap.mul ℝ R) α β) γ) =
      wedge (ContinuousLinearMap.mul ℝ R) α
        (wedge (ContinuousLinearMap.mul ℝ R) β γ) := by
  ext v
  rw [degreeCast_apply]
  have h := wedge_assoc_apply
    (ContinuousLinearMap.mul ℝ R) (ContinuousLinearMap.mul ℝ R)
    (ContinuousLinearMap.mul ℝ R) (ContinuousLinearMap.mul ℝ R)
    (by intro a b c; exact mul_assoc a b c) α β γ
    (v ∘ finCongr (Nat.add_assoc p q r))
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h

private theorem wedge_mul_right_degreeCast {p m n : ℕ} (h : m = n)
    (α : E [⋀^Fin p]→L[ℝ] R)
    (β : E [⋀^Fin m]→L[ℝ] R) :
    degreeCast (congrArg (p + ·) h)
      (wedge (ContinuousLinearMap.mul ℝ R) α β) =
      wedge (ContinuousLinearMap.mul ℝ R) α (degreeCast h β) := by
  cases h
  rfl

private theorem degreeCast_three {a b c d : ℕ}
    (h₁ : a = b) (h₂ : b = c) (h₃ : c = d)
    (ω : E [⋀^Fin a]→L[ℝ] R) :
    degreeCast (h₁.trans (h₂.trans h₃)) ω =
      degreeCast h₃ (degreeCast h₂ (degreeCast h₁ ω)) := by
  cases h₁
  cases h₂
  cases h₃
  rfl

private theorem degreeCast_two {a b c : ℕ}
    (h₁ : a = b) (h₂ : b = c)
    (ω : E [⋀^Fin a]→L[ℝ] R) :
    degreeCast (h₁.trans h₂) ω = degreeCast h₂ (degreeCast h₁ ω) := by
  cases h₁
  cases h₂
  rfl

/-- Multiplication of two ordered curvature powers gives the next combined
power, with the equality of finite slot degrees made explicit. -/
theorem curvaturePowerForm_mul (Γ : Form (E := E) (A := R))
    (i j : ℕ) (x : E) :
    degreeCast (powerDegree_concat i j)
      (wedge (ContinuousLinearMap.mul ℝ R)
        (curvaturePowerForm Γ i x) (curvaturePowerForm Γ j x)) =
      curvaturePowerForm Γ (concatIndex i j) x := by
  induction i with
  | zero =>
      change degreeCast (powerDegree_concat 0 j)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (curvatureForm Γ x) (curvaturePowerForm Γ j x)) =
        curvaturePowerForm Γ (j + 1) x
      rfl
  | succ i ih =>
      let F := curvatureForm Γ x
      let Pi := curvaturePowerForm Γ i x
      let Pj := curvaturePowerForm Γ j x
      let hAssoc := Nat.add_assoc 2 (powerDegree i) (powerDegree j)
      let hInner := congrArg (2 + ·) (powerDegree_concat i j)
      have hEnd : 2 + powerDegree (concatIndex i j) =
          powerDegree (concatIndex (i + 1) j) := rfl
      have hcast :
          degreeCast (powerDegree_concat (i + 1) j)
            (wedge (ContinuousLinearMap.mul ℝ R)
              (wedge (ContinuousLinearMap.mul ℝ R) F Pi) Pj) =
          degreeCast hEnd (degreeCast hInner (degreeCast hAssoc
            (wedge (ContinuousLinearMap.mul ℝ R)
              (wedge (ContinuousLinearMap.mul ℝ R) F Pi) Pj))) := by
        exact (show degreeCast (powerDegree_concat (i + 1) j) _ =
          degreeCast (hAssoc.trans (hInner.trans hEnd)) _ by
            congr 1) |>.trans (degreeCast_three hAssoc hInner hEnd _)
      change degreeCast (powerDegree_concat (i + 1) j)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (wedge (ContinuousLinearMap.mul ℝ R) F Pi) Pj) = _
      rw [hcast, wedge_mul_assoc_cast,
        wedge_mul_right_degreeCast (powerDegree_concat i j) F
          (wedge (ContinuousLinearMap.mul ℝ R) Pi Pj), ih]
      change degreeCast hEnd
        (wedge (ContinuousLinearMap.mul ℝ R) F
          (curvaturePowerForm Γ (concatIndex i j) x)) =
        curvaturePowerForm Γ (concatIndex (i + 1) j) x
      rfl

/-- Reassociating a one-form followed by two curvature powers gives the
one-form wedged with their combined power. This is algebra-valued and does
not need trace cyclicity. -/
theorem connection_curvaturePowerForm_mul
    (Γ θ : Form (E := E) (A := R)) (i j : ℕ) (x : E) :
    degreeCast
      ((Nat.add_assoc 1 (powerDegree i) (powerDegree j)).trans
        (congrArg (1 + ·) (powerDegree_concat i j)))
      (wedge (ContinuousLinearMap.mul ℝ R)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (connectionForm θ x) (curvaturePowerForm Γ i x))
        (curvaturePowerForm Γ j x)) =
      wedge (ContinuousLinearMap.mul ℝ R)
        (connectionForm θ x) (curvaturePowerForm Γ (concatIndex i j) x) := by
  let hAssoc := Nat.add_assoc 1 (powerDegree i) (powerDegree j)
  let hInner := congrArg (1 + ·) (powerDegree_concat i j)
  rw [degreeCast_two hAssoc hInner]
  rw [wedge_mul_assoc_cast]
  rw [wedge_mul_right_degreeCast (powerDegree_concat i j)
    (connectionForm θ x)
    (wedge (ContinuousLinearMap.mul ℝ R)
      (curvaturePowerForm Γ i x) (curvaturePowerForm Γ j x))]
  rw [curvaturePowerForm_mul]

end
end QuaternionicSymmetry.LocalCurvaturePowerMultiplication
