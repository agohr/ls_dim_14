import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveConnectionGeneratorSmooth
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensor

/-! Joint C∞ regularity of the actual connection generator in the
second CP¹ affine coordinate, including the matrix-coordinate swap. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondGeneratorSmooth

open scoped ContDiff Manifold Matrix Quaternion
open FourDimensionalHalfSpinProjectiveJointGeneratorSmooth
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinMatrixConnection
  ManifoldQuaternionicConnection

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

private def swapMatrixLinear : Mat2 →ₗ[ℝ] Mat2 where
  toFun A := coordinateSwap * A * coordinateSwap
  map_add' A B := by simp [mul_add, add_mul]
  map_smul' c A := by simp [smul_eq_mul, mul_assoc]

private def swapMatrixCLM : Mat2 →L[ℝ] Mat2 :=
  ⟨swapMatrixLinear, swapMatrixLinear.continuous_of_finiteDimensional⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private def chartTangentSet (p : M) : Set ((ℍ × ℂ) × (ℍ × ℂ)) :=
  ((extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ) ×ˢ Set.univ

theorem second_connection_generator_smooth (p : M) :
    ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        secondChartGenerator (spinorMatrixForm Q D p z.1.1 z.2.1) z.1.2)
      (chartTangentSet p) := by
  have hpos : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) => z.1.1) (chartTangentSet p) := by
    fun_prop
  have hu : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) => z.2.1) (chartTangentSet p) := by
    fun_prop
  have hz : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) => z.1.2) (chartTangentSet p) := by
    fun_prop
  have hform : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        spinorMatrixConnectionForm Q D p z.1.1)
      (chartTangentSet p) :=
    (spinorMatrixConnectionForm_smooth Q D p).comp hpos (by
      intro z hz
      exact hz.1.1)
  have hmat := hform.clm_apply hu
  have hswap : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        swapMatrixCLM (spinorMatrixForm Q D p z.1.1 z.2.1))
      (chartTangentSet p) :=
    swapMatrixCLM.contDiff.contDiffOn.comp hmat (by
      intro z hz
      exact Set.mem_univ _)
  convert affineGenerator_smooth.contDiffOn.comp
    (hswap.prodMk hz) (by intro z hz; exact Set.mem_univ _) using 1

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondGeneratorSmooth
