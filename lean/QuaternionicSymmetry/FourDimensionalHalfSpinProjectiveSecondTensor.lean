import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChartSwapConnection
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveLocalAHS

/-! The second CP¹ affine chart has its own independently defined local
connection graph and antipodal-Hopf horizontal base complex structure. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensor

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorLocalAlmostComplex
  FourDimensionalHalfSpinMatrixConnection
  ManifoldQuaternionicConnection

noncomputable section

private def swapMatrixLinear : Mat2 →ₗ[ℝ] Mat2 where
  toFun A := coordinateSwap * A * coordinateSwap
  map_add' A B := by
    simp [mul_add, add_mul]
  map_smul' c A := by
    simp [smul_eq_mul, mul_assoc]

def secondChartGeneratorLinear (z : ℂ) : Mat2 →ₗ[ℝ] ℂ :=
  (affineGeneratorRealLinear z).comp swapMatrixLinear

theorem secondChartGeneratorLinear_apply (A : Mat2) (z : ℂ) :
    secondChartGeneratorLinear z A = secondChartGenerator A z := rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def secondLocalConnectionGenerator (p : M) (y : ℍ) (z : ℂ) :
    ℍ →ₗ[ℝ] ℂ :=
  (secondChartGeneratorLinear z).comp
    (spinorMatrixConnectionForm Q D p y).toLinearMap

theorem secondLocalConnectionGenerator_apply (p : M) (y u : ℍ) (z : ℂ) :
    secondLocalConnectionGenerator Q D p y z u =
      secondChartGenerator (spinorMatrixForm Q D p y u) z := rfl

def secondLocalActualProjectiveAHS (p : M) (y : ℍ) (z : ℂ) :
    (ℍ × ℂ) →ₗ[ℝ] (ℍ × ℂ) :=
  let a := antipodalCoefficient (hopfSphere ![z,1] (by simp))
  graphComplex (chartBaseComplex Q p y a)
    (secondLocalConnectionGenerator Q D p y z)

theorem secondLocalActualProjectiveAHS_sq (p : M) (y : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ)
    (v : ℍ × ℂ) :
    secondLocalActualProjectiveAHS Q D p y z
      (secondLocalActualProjectiveAHS Q D p y z v) = -v := by
  exact graphComplex_sq _ _
    (chartBaseComplex_sq Q p y hy
      (antipodalCoefficient (hopfSphere ![z,1] (by simp)))) v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensor
