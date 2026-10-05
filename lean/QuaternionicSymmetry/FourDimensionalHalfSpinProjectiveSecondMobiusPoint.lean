import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondAction

/-! The actual half-spin projective action on `[w:1]` is equality of
projective points, not merely equality of second-affine ratios. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondMobiusPoint

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveSecondMobius
  FourDimensionalHalfSpinProjectiveSecondAction
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  ComplexProjectiveTopology

noncomputable section

theorem projectiveHalfSpin_secondPoint (q : unitary ℍ) (w : ℂ)
    (hden : secondDen (FourDimensionalHalfSpinMatrix.halfSpinMatrix (q : ℍ)) w ≠ 0) :
    projectiveHalfSpin q (secondAffineSpinorPoint w) =
      secondAffineSpinorPoint
        (secondMobius (FourDimensionalHalfSpinMatrix.halfSpinMatrix (q : ℍ)) w) := by
  have hp : projectiveHalfSpin q (secondAffineSpinorPoint w) ∈
      (projectiveChart 1 1).source := by
    simpa [projectiveChart_source] using
      secondAffineSpinorPoint_action_mem q w hden
  calc
    projectiveHalfSpin q (secondAffineSpinorPoint w) =
        (projectiveChart 1 1).symm
          ((projectiveChart 1 1)
            (projectiveHalfSpin q (secondAffineSpinorPoint w))) :=
      ((projectiveChart 1 1).left_inv hp).symm
    _ = (projectiveChart 1 1).symm
          ![secondMobius
            (FourDimensionalHalfSpinMatrix.halfSpinMatrix (q : ℍ)) w] := by
      congr 1
      funext i
      fin_cases i
      exact secondAffineSpinorPoint_action_ratio q w hden
    _ = secondAffineSpinorPoint _ := rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondMobiusPoint
