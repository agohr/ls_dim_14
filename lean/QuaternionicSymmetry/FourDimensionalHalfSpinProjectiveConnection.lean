import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveDescent
import QuaternionicSymmetry.FourDimensionalHalfSpinMatrixConnection

/-! The actual adapted metric connection induces a local CP¹ tangent
generator via its independently constructed left half-spin matrix.  The
formula is the derivative of homogeneous-coordinate projectivization. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveConnection

open scoped Quaternion Manifold Matrix ContDiff
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveDescent
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinLieProjection
  FourDimensionalHalfSpinMatrix
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def projectiveConnectionGenerator (p : M) (y u : ℍ) (z : ℂ) : ℂ :=
  affineGenerator (spinorMatrixForm Q D p y u) z

/-- The local CP¹ connection vector field is computed directly from the
left quaternion coefficient, including its precise affine-chart sign. -/
theorem projectiveConnectionGenerator_formula (p : M) (y u : ℍ) (z : ℂ) :
    projectiveConnectionGenerator Q D p y u z =
      second (leftSpinorForm Q D p y u) +
      (star (first (leftSpinorForm Q D p y u)) -
        first (leftSpinorForm Q D p y u)) * z +
      star (second (leftSpinorForm Q D p y u)) * z ^ 2 := by
  exact affineGenerator_halfSpinMatrix _ z

/-- Literal derivative in the genuine CP¹ affine chart of the spinor
deformation determined by the actual metric connection coefficient. -/
theorem projectiveConnectionGenerator_is_chartDerivative
    (p : M) (y u : ℍ) (z : ℂ) :
    HasDerivAt
      (affineLinearFlow (spinorMatrixForm Q D p y u) z)
      (projectiveConnectionGenerator Q D p y u z) 0 :=
  affineLinearFlow_hasDerivAt _ z

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveConnection
