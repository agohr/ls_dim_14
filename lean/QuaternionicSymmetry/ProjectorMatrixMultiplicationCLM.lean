import QuaternionicSymmetry.ProjectorPeirceContinuousProjection

/-! Explicit continuous real-bilinear matrix multiplication in the
existing finite-dimensional operator-norm ambient matrix space. -/

namespace QuaternionicSymmetry.ProjectorMatrixMultiplicationCLM

open Matrix
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

private def rightLinear (n : ℕ) (P : Mat n) : Mat n →ₗ[ℝ] Mat n where
  toFun := fun A => P * A
  map_add' := by intro A B; simp [mul_add]
  map_smul' := by intro c A; simp [Matrix.mul_smul]

private def leftLinear (n : ℕ) : Mat n →ₗ[ℝ] (Mat n →L[ℝ] Mat n) where
  toFun := fun P => (rightLinear n P).toContinuousLinearMap
  map_add' := by
    intro P Q
    apply ContinuousLinearMap.ext
    intro A
    simp [rightLinear, add_mul]
  map_smul' := by
    intro c P
    apply ContinuousLinearMap.ext
    intro A
    simp [rightLinear, Matrix.smul_mul]

def matrixMulCLM (n : ℕ) : Mat n →L[ℝ] Mat n →L[ℝ] Mat n :=
  (leftLinear n).toContinuousLinearMap

@[simp] theorem matrixMulCLM_apply (n : ℕ) (P A : Mat n) :
    matrixMulCLM n P A = P * A := rfl

end
end QuaternionicSymmetry.ProjectorMatrixMultiplicationCLM
