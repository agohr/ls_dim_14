import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineHorizontal
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensor

/-! The second literal affine spinor representative `[z,1]` has the
same normalized-Hopf horizontal connection formula, including its
independently defined second-chart projective generator. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondHorizontal

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinHopfNormalizedConnection
  FourDimensionalHalfSpinHopfScalarDerivative
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinMatrixConnection
  ManifoldQuaternionicAdjointConnection
  QuaternionicUnitScalarIsometries

noncomputable section

theorem second_homogeneous_horizontal_decomposition (A : Mat2) (z : ℂ) :
    -(A *ᵥ ![z,1]) =
      (-(A *ᵥ ![z,1]) 1) • ![z,1] +
        ![-secondChartGenerator A z, 0] := by
  ext j
  fin_cases j <;>
    simp [secondChartGenerator, coordinateSwap,
      FourDimensionalHalfSpinProjectiveGenerator.affineGenerator,
      Matrix.mulVec, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;> ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem normalizedSpinorHopf_second_horizontal
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    fderiv ℝ normalizedSpinorHopf ![z,1]
      ![-(secondLocalConnectionGenerator Q D p y z u), 0] =
      -pureScalar (inducedForm Q D p y u
        (hopfSphere ![z,1] (by simp)).1) := by
  let A := spinorMatrixForm Q D p y u
  let s : Spinor := ![z,1]
  have hs : s ≠ 0 := by simp [s]
  have hconn := normalizedSpinorHopf_horizontal_derivative Q D p y u hy s hs
  have hdecomp := second_homogeneous_horizontal_decomposition A z
  change -(A *ᵥ s) = _ at hdecomp
  rw [hdecomp, map_add,
    normalizedSpinorHopf_scalar_derivative s hs (-(A *ᵥ s) 1), zero_add]
    at hconn
  simpa only [s, A, secondLocalConnectionGenerator_apply] using hconn

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondHorizontal
