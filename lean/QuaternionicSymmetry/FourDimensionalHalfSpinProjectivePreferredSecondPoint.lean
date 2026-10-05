import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredZeroTarget

/-! The other actual selected CP¹ affine chart reconstructs the fiber as
`[w:1]`, including its south-pole center. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredSecondPoint

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveMobiusAction
  ComplexProjectiveTopology

noncomputable section

def secondAffineSpinorPoint (w : ℂ) :
    FourDimensionalHalfSpinProjective.ProjectiveSpinor :=
  (projectiveChart 1 1).symm ![w]

theorem preferred_one_secondPoint
    (s : FourDimensionalHalfSpinProjective.ProjectiveSpinor)
    (hone : preferredProjectiveChartIndex s = 1) :
    s = secondAffineSpinorPoint (preferredProjectiveScalar s) := by
  have hs : s ∈ (projectiveChart 1 1).source := by
    simpa [projectiveChart_source, ← hone] using
      preferredProjectiveChartIndex_mem s
  have hw : (projectiveChart 1 1) s =
      ![preferredProjectiveScalar s] := by
    funext i
    fin_cases i
    simp [preferredProjectiveScalar, hone]
  calc
    s = (projectiveChart 1 1).symm ((projectiveChart 1 1) s) :=
      ((projectiveChart 1 1).left_inv hs).symm
    _ = secondAffineSpinorPoint (preferredProjectiveScalar s) := by
      rw [hw]
      rfl

theorem secondAffineSpinorPoint_mk (w : ℂ) :
    secondAffineSpinorPoint w =
      Projectivization.mk ℂ ![w,1] (by simp) := by
  rw [secondAffineSpinorPoint, projectiveChart_symm_apply]
  unfold euclideanPoint homogeneousVector
  congr 1
  funext i
  fin_cases i
  · rw [Fin.insertNth_apply_below (h := by decide)]
    simp
  · simp [Fin.insertNth_apply_same]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredSecondPoint
