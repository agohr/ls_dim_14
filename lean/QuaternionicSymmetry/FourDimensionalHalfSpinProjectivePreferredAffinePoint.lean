import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredChartTangent
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthDerivative

/-! The selected first affine chart really reconstructs the total-space
projective fiber as `[1:z]`. This is needed when specializing the actual
core transition and its derivative to the chosen chart at a point. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredAffinePoint

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinProjectiveMobiusAction
  ComplexProjectiveTopology

noncomputable section

theorem preferred_zero_affinePoint
    (s : FourDimensionalHalfSpinProjective.ProjectiveSpinor)
    (hzero : preferredProjectiveChartIndex s = 0) :
    s = affineSpinorPoint (preferredProjectiveScalar s) := by
  have hs : s ∈ (projectiveChart 1 0).source := by
    simpa [projectiveChart_source, ← hzero] using
      preferredProjectiveChartIndex_mem s
  have hw : (projectiveChart 1 0) s =
      ![preferredProjectiveScalar s] := by
    funext i
    fin_cases i
    simp [preferredProjectiveScalar, hzero]
  calc
    s = (projectiveChart 1 0).symm ((projectiveChart 1 0) s) :=
      ((projectiveChart 1 0).left_inv hs).symm
    _ = affineSpinorPoint (preferredProjectiveScalar s) := by
      rw [hw, affineSpinorPoint_eq_projectiveChart]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredAffinePoint
