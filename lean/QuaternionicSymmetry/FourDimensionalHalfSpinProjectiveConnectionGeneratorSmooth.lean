import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointGeneratorSmooth
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveLocalAHS

/-! Joint C∞ regularity of the actual projectivized adapted-connection
generator in base position, base direction, and CP¹ affine coordinate. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveConnectionGeneratorSmooth

open scoped ContDiff Manifold Matrix Quaternion
open FourDimensionalHalfSpinProjectiveJointGeneratorSmooth
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinMatrixConnection
  ManifoldQuaternionicConnection

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private def chartTangentSet (p : M) : Set ((ℍ × ℂ) × (ℍ × ℂ)) :=
  ((extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ) ×ˢ Set.univ

theorem first_connection_generator_smooth (p : M) :
    ContDiffOn ℝ ∞
      (fun z : (ℍ × ℂ) × (ℍ × ℂ) =>
        projectiveConnectionGenerator Q D p z.1.1 z.2.1 z.1.2)
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
  exact affineGenerator_smooth.contDiffOn.comp
    (hmat.prodMk hz) (by intro z hz; exact Set.mem_univ _)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveConnectionGeneratorSmooth
