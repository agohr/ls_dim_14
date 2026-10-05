import QuaternionicSymmetry.ProjectorPeirceChartDerivative

/-! The concrete Peirce map is a continuous real-linear operator on the
finite-dimensional ambient complex matrix space with its existing norm. -/

namespace QuaternionicSymmetry.ProjectorPeirceContinuousProjection

open Matrix ProjectorPeirceTangentProjection
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

def tangentPartCLM (n : ℕ) (P : Mat n) : Mat n →L[ℝ] Mat n :=
  (show Mat n →ₗ[ℝ] Mat n from {
    toFun := tangentPart P
    map_add' := by
      intro A B
      simp only [tangentPart, mul_add, add_mul, smul_add]
      abel
    map_smul' := by
      intro c A
      simp [tangentPart, smul_sub, smul_add, Matrix.mul_smul, Matrix.smul_mul]
  }).toContinuousLinearMap

@[simp] theorem tangentPartCLM_apply (n : ℕ) (P A : Mat n) :
    tangentPartCLM n P A = tangentPart P A := rfl

end
end QuaternionicSymmetry.ProjectorPeirceContinuousProjection
