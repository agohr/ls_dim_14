import QuaternionicSymmetry.FourDimensionalHalfSpinHopfScalarDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveConnection

/-! The homogeneous spinor horizontal direction differs from the actual
first affine-coordinate horizontal direction only by an infinitesimal
complex rescaling.  The normalized Hopf differential kills that rescaling. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineHorizontal

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinHopfNormalizedConnection
  FourDimensionalHalfSpinHopfScalarDerivative
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinMatrixConnection
  ManifoldQuaternionicAdjointConnection
  QuaternionicUnitScalarIsometries

noncomputable section

theorem homogeneous_horizontal_decomposition (A : Mat2) (z : ℂ) :
    -(A *ᵥ ![1,z]) =
      (-(A *ᵥ ![1,z]) 0) • ![1,z] +
        ![0, -affineGenerator A z] := by
  ext j
  fin_cases j <;>
    simp [affineGenerator, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;> ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem normalizedSpinorHopf_affine_horizontal
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    fderiv ℝ normalizedSpinorHopf ![1,z]
      ![0, -(projectiveConnectionGenerator Q D p y u z)] =
      -pureScalar (inducedForm Q D p y u
        (hopfSphere ![1,z] (by simp)).1) := by
  let A := spinorMatrixForm Q D p y u
  let s : Spinor := ![1,z]
  have hs : s ≠ 0 := by simp [s]
  have hconn := normalizedSpinorHopf_horizontal_derivative Q D p y u hy s hs
  have hdecomp := homogeneous_horizontal_decomposition A z
  change -(A *ᵥ s) = _ at hdecomp
  rw [hdecomp, map_add,
    normalizedSpinorHopf_scalar_derivative s hs (-(A *ᵥ s) 0), zero_add]
    at hconn
  simpa only [s, A, projectiveConnectionGenerator] using hconn

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineHorizontal
