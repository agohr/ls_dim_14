import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondGeneratorSmooth
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBaseTensorSmooth

/-! Joint smoothness of the first local projective almost-complex tensor,
evaluated on an actual tangent-chart direction. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFirstTensorSmooth

open scoped ContDiff Manifold Matrix Quaternion
open FourDimensionalHalfSpinProjectiveConnectionGeneratorSmooth
  FourDimensionalHalfSpinProjectiveBaseTensorSmooth
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveConnection
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

theorem first_local_tensor_apply_smooth (p : M) :
    ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        localActualProjectiveAHS Q D p z.1.1 z.1.2 z.2)
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
          (antipodalCoefficient (hopfSphere ![1,z.1.2] (by simp)))) S :=
    (first_base_smooth Q p).comp hpoint (by intro z hz; exact hz.1)
  have hBu := hB.clm_apply hu
  have hK : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        projectiveConnectionGenerator Q D p z.1.1 z.2.1 z.1.2) S :=
    first_connection_generator_smooth Q D p
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
  have hKBu : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        projectiveConnectionGenerator Q D p z.1.1
          (chartBaseComplex Q p z.1.1
            (antipodalCoefficient (hopfSphere ![1,z.1.2] (by simp))) z.2.1)
          z.1.2) S := by
    exact affineGenerator_smooth.contDiffOn.comp
      (hmatBu.prodMk hz) (by intro z hz; exact Set.mem_univ _)
  have hsecond : ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        Complex.I * (z.2.2 +
          projectiveConnectionGenerator Q D p z.1.1 z.2.1 z.1.2) -
        projectiveConnectionGenerator Q D p z.1.1
          (chartBaseComplex Q p z.1.1
            (antipodalCoefficient (hopfSphere ![1,z.1.2] (by simp))) z.2.1)
          z.1.2) S :=
    ((contDiffOn_const.mul (hv.add hK))).sub hKBu
  convert hBu.prodMk hsecond using 1

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFirstTensorSmooth
