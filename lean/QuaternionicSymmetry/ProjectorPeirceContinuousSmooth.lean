import QuaternionicSymmetry.ProjectorPeirceContinuousProjection
import QuaternionicSymmetry.ProjectorMatrixMultiplicationCLM
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! The actual Peirce ambient projection varies differentiably as a
continuous real-linear operator with the projector matrix. -/

namespace QuaternionicSymmetry.ProjectorPeirceContinuousSmooth

open Matrix ProjectorPeirceTangentProjection
open ProjectorPeirceContinuousProjection
open ProjectorMatrixMultiplicationCLM
open scoped Matrix.Norms.Operator
noncomputable section
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem tangentPartCLM_eq_mul (n : ℕ) (P : Mat n) :
    tangentPartCLM n P =
      matrixMulCLM n P +
      (matrixMulCLM n).flip P -
        2 • ((matrixMulCLM n P).comp
          ((matrixMulCLM n).flip P)) := by
  apply ContinuousLinearMap.ext
  intro A
  change tangentPart P A = P * A + A * P - 2 • (P * (A * P))
  simp only [tangentPart, Matrix.mul_assoc]

theorem tangentPartCLM_differentiableAt (n : ℕ) (P : Mat n) :
    DifferentiableAt ℝ (tangentPartCLM n) P := by
  letI : NormedSpace ℝ (Mat n) := inferInstance
  letI : NormedSpace ℝ (Mat n →L[ℝ] Mat n) := inferInstance
  let mul : Mat n →L[ℝ] Mat n →L[ℝ] Mat n := matrixMulCLM n
  have hleft : DifferentiableAt ℝ (fun Q : Mat n => mul Q) P :=
    mul.differentiableAt
  have hright : DifferentiableAt ℝ (fun Q : Mat n => mul.flip Q) P :=
    mul.flip.differentiableAt
  have hcomp : DifferentiableAt ℝ
      (fun Q : Mat n => (mul Q).comp (mul.flip Q)) P :=
    hleft.clm_comp hright
  have hsum : DifferentiableAt ℝ
      (fun Q : Mat n => mul Q + mul.flip Q) P := hleft.add hright
  have htwo : DifferentiableAt ℝ
      (fun Q : Mat n => (2 : ℝ) • (mul Q).comp (mul.flip Q)) P :=
    by simpa only [Pi.smul_apply] using hcomp.const_smul (2 : ℝ)
  have h : DifferentiableAt ℝ
      (fun Q : Mat n => mul Q + mul.flip Q -
        (2 : ℝ) • (mul Q).comp (mul.flip Q)) P := hsum.sub htwo
  convert h using 1
  funext Q
  rw [tangentPartCLM_eq_mul]
  simp only [mul, two_nsmul, two_smul]

end
end QuaternionicSymmetry.ProjectorPeirceContinuousSmooth
