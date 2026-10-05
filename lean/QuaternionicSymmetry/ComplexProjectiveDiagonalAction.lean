import QuaternionicSymmetry.ComplexProjectivePolynomialLocus
import QuaternionicSymmetry.TorusLaurentRepresentation

/-! The literal diagonal complex-torus action on the actual projective
space. Integral coordinate weights give invertible linear maps, and their
projectivizations obey the group laws. Preservation of a particular image
is a separate theorem. -/
namespace QuaternionicSymmetry.ComplexProjectiveDiagonalAction

open ComplexProjectiveTopology TorusLaurentRepresentation
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {r d : ℕ}

def diagonalEquiv (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) :
    Coord d ≃ₗ[ℂ] Coord d where
  toFun v i := (complexWeightCharacter (μ i) z : ℂ) * v i
  invFun v i := ((complexWeightCharacter (μ i) z)⁻¹ : ℂˣ) * v i
  left_inv v := by ext i; simp [← mul_assoc]
  right_inv v := by ext i; simp [← mul_assoc]
  map_add' v w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp [mul_left_comm]

@[simp] theorem diagonalEquiv_apply
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) (v : Coord d)
    (i : Fin (d + 1)) :
    diagonalEquiv μ z v i = (complexWeightCharacter (μ i) z : ℂ) * v i := rfl

@[simp] theorem diagonalEquiv_one
    (μ : Fin (d + 1) → Fin r → ℤ) (v : Coord d) :
    diagonalEquiv μ 1 v = v := by ext i; simp

theorem diagonalEquiv_mul
    (μ : Fin (d + 1) → Fin r → ℤ) (z w : ComplexTorus r) (v : Coord d) :
    diagonalEquiv μ (z * w) v = diagonalEquiv μ z (diagonalEquiv μ w v) := by
  ext i
  simp [mul_assoc]

def projectiveAction (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) :
    Space d → Space d :=
  Projectivization.map (diagonalEquiv μ z).toLinearMap (diagonalEquiv μ z).injective

theorem projectiveAction_mk
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (v : Coord d) (hv : v ≠ 0) :
    projectiveAction μ z (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (diagonalEquiv μ z v)
        ((diagonalEquiv μ z).map_ne_zero_iff.mpr hv) := rfl

@[simp] theorem projectiveAction_one
    (μ : Fin (d + 1) → Fin r → ℤ) (x : Space d) :
    projectiveAction μ 1 x = x := by
  induction x using Projectivization.ind with
  | h v hv => simp [projectiveAction_mk]

theorem projectiveAction_mul
    (μ : Fin (d + 1) → Fin r → ℤ) (z w : ComplexTorus r) (x : Space d) :
    projectiveAction μ (z * w) x = projectiveAction μ z (projectiveAction μ w x) := by
  induction x using Projectivization.ind with
  | h v hv => simp only [projectiveAction_mk, diagonalEquiv_mul]

@[simp] theorem projectiveAction_inv_apply
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) (x : Space d) :
    projectiveAction μ z⁻¹ (projectiveAction μ z x) = x := by
  rw [← projectiveAction_mul, inv_mul_cancel, projectiveAction_one]

@[simp] theorem projectiveAction_apply_inv
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) (x : Space d) :
    projectiveAction μ z (projectiveAction μ z⁻¹ x) = x := by
  rw [← projectiveAction_mul, mul_inv_cancel, projectiveAction_one]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalAction
