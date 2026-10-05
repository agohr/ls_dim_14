import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFirstTensorSmooth

/-! Joint smoothness of the independently defined second affine-chart
projective almost-complex tensor on position-and-direction coordinates. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensorSmooth

open scoped ContDiff Manifold Matrix Quaternion
open FourDimensionalHalfSpinProjectiveSecondGeneratorSmooth
  FourDimensionalHalfSpinProjectiveBaseTensorSmooth
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinProjectiveJointGeneratorSmooth
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private def chartTangentSet (p : M) : Set ((ℍ × ℂ) × (ℍ × ℂ)) :=
  ((extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ) ×ˢ Set.univ

local instance : NormedRing FourDimensionalHalfSpinProjectiveGenerator.Mat2 :=
  Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ FourDimensionalHalfSpinProjectiveGenerator.Mat2 :=
  Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ FourDimensionalHalfSpinProjectiveGenerator.Mat2 :=
  NormedAlgebra.toNormedSpace _

private def swapMatrixLinear : FourDimensionalHalfSpinProjectiveGenerator.Mat2 →ₗ[ℝ]
    FourDimensionalHalfSpinProjectiveGenerator.Mat2 where
  toFun A := coordinateSwap * A * coordinateSwap
  map_add' A B := by simp [mul_add, add_mul]
  map_smul' c A := by simp [smul_eq_mul, mul_assoc]

private def swapMatrixCLM : FourDimensionalHalfSpinProjectiveGenerator.Mat2 →L[ℝ]
    FourDimensionalHalfSpinProjectiveGenerator.Mat2 :=
  ⟨swapMatrixLinear, swapMatrixLinear.continuous_of_finiteDimensional⟩

theorem second_local_tensor_apply_smooth (p : M) :
    ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        secondLocalActualProjectiveAHS Q D p z.1.1 z.1.2 z.2)
      (chartTangentSet p) := by
  let S := chartTangentSet p
  have hpoint : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) => z.1) S := by fun_prop
  have hu : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) => z.2.1) S := by fun_prop
  have hv : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) => z.2.2) S := by fun_prop
  have hB : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        chartBaseComplex Q p z.1.1
          (antipodalCoefficient (hopfSphere ![z.1.2,1] (by simp)))) S :=
    (second_base_smooth Q p).comp hpoint (by intro z hz; exact hz.1)
  have hBu := hB.clm_apply hu
  have hK : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        secondChartGenerator (spinorMatrixForm Q D p z.1.1 z.2.1) z.1.2) S :=
    second_connection_generator_smooth Q D p
  have hpos : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) => z.1.1) S := by fun_prop
  have hform : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        spinorMatrixConnectionForm Q D p z.1.1) S :=
    (spinorMatrixConnectionForm_smooth Q D p).comp hpos (by
      intro z hz
      exact hz.1.1)
  have hmatBu := hform.clm_apply hBu
  have hz : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) => z.1.2) S := by fun_prop
  have hswap : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        swapMatrixCLM (spinorMatrixForm Q D p z.1.1
          (chartBaseComplex Q p z.1.1
            (antipodalCoefficient (hopfSphere ![z.1.2,1] (by simp))) z.2.1))) S :=
    swapMatrixCLM.contDiff.contDiffOn.comp hmatBu (by
      intro z hz
      exact Set.mem_univ _)
  have hKBu : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        secondChartGenerator (spinorMatrixForm Q D p z.1.1
          (chartBaseComplex Q p z.1.1
            (antipodalCoefficient (hopfSphere ![z.1.2,1] (by simp))) z.2.1))
          z.1.2) S := by
    exact affineGenerator_smooth.contDiffOn.comp
      (hswap.prodMk hz) (by intro z hz; exact Set.mem_univ _)
  have hsecond : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        Complex.I * (z.2.2 +
          secondChartGenerator (spinorMatrixForm Q D p z.1.1 z.2.1) z.1.2) -
        secondChartGenerator (spinorMatrixForm Q D p z.1.1
          (chartBaseComplex Q p z.1.1
            (antipodalCoefficient (hopfSphere ![z.1.2,1] (by simp))) z.2.1))
          z.1.2) S :=
    ((contDiffOn_const.mul (hv.add hK))).sub hKBu
  convert hBu.prodMk hsecond using 1

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensorSmooth
