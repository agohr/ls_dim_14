import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveConnection

/-! Fiberwise complex regularity of the independently constructed
projective-spinor connection vector field. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGeneratorSmooth

open scoped Quaternion Manifold Matrix ContDiff
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinMatrixConnection
  ManifoldQuaternionicConnection

noncomputable section

theorem affineGenerator_contDiff (A : Mat2) :
    ContDiff ℂ ∞ (affineGenerator A) := by
  unfold affineGenerator
  fun_prop

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- Each fiber generator of the actual metric-induced projective
connection is complex smooth (hence holomorphic) in the CP¹ affine chart. -/
theorem projectiveConnectionGenerator_fiber_contDiff
    (p : M) (y u : ℍ) :
    ContDiff ℂ ∞ (projectiveConnectionGenerator Q D p y u) :=
  affineGenerator_contDiff _

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGeneratorSmooth
