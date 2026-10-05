import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredSecondPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthDerivative

/-! The half-spin action from `[w:1]` to `[1:z]` is a genuine equality
of projective points, including both affine poles. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseMixedPoint

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveSecondMobius
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinProjectiveNorthDerivative
  ComplexProjectiveTopology

noncomputable section

theorem secondSpinorPoint_reverse_action_mem (q : unitary ℍ) (w : ℂ)
    (hden : reverseDen (halfSpinMatrix (q : ℍ)) w ≠ 0) :
    projectiveHalfSpin q (secondAffineSpinorPoint w) ∈ affineDomain 1 0 := by
  rw [secondAffineSpinorPoint_mk, projectiveHalfSpin_mk]
  apply (mem_affineDomain_mk 1 0 _ _).2
  simpa [reverseDen, secondNum, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] using hden

theorem secondSpinorPoint_reverse_action_ratio (q : unitary ℍ) (w : ℂ)
    (hden : reverseDen (halfSpinMatrix (q : ℍ)) w ≠ 0) :
    (projectiveChart 1 0)
      (projectiveHalfSpin q (secondAffineSpinorPoint w)) 0 =
        reverseMobius (halfSpinMatrix (q : ℍ)) w := by
  let G := halfSpinMatrix (q : ℍ)
  let v := G *ᵥ ![w,1]
  have hden' : v 0 ≠ 0 := by
    simpa [v, G, reverseDen, secondNum, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using hden
  have hv : v ≠ 0 := by
    intro h
    exact hden' (by simpa [v] using congrFun h 0)
  have hpoint : projectiveHalfSpin q (secondAffineSpinorPoint w) =
      Projectivization.mk ℂ v hv := by
    rw [secondAffineSpinorPoint_mk, projectiveHalfSpin_mk]
    rfl
  have hp := secondSpinorPoint_reverse_action_mem q w hden
  rw [projectiveChart_apply 1 0 _ hp]
  change affineRatio 1 0
    ⟨projectiveHalfSpin q (secondAffineSpinorPoint w), hp⟩ 1 = _
  have hsub :
      (⟨projectiveHalfSpin q (secondAffineSpinorPoint w), hp⟩ :
        {p : Space 1 // p ∈ affineDomain 1 0}) =
      ⟨Projectivization.mk ℂ v hv,
        (mem_affineDomain_mk 1 0 v hv).2 hden'⟩ :=
    Subtype.ext hpoint
  rw [hsub, affineRatio_mk 1 0 1 v hv hden']
  simp [reverseMobius, reverseNum, reverseDen, secondNum, secondDen,
    v, G, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem projectiveHalfSpin_reversePoint (q : unitary ℍ) (w : ℂ)
    (hden : reverseDen (halfSpinMatrix (q : ℍ)) w ≠ 0) :
    projectiveHalfSpin q (secondAffineSpinorPoint w) =
      affineSpinorPoint (reverseMobius (halfSpinMatrix (q : ℍ)) w) := by
  have hp : projectiveHalfSpin q (secondAffineSpinorPoint w) ∈
      (projectiveChart 1 0).source := by
    simpa [projectiveChart_source] using
      secondSpinorPoint_reverse_action_mem q w hden
  calc
    projectiveHalfSpin q (secondAffineSpinorPoint w) =
        (projectiveChart 1 0).symm
          ((projectiveChart 1 0)
            (projectiveHalfSpin q (secondAffineSpinorPoint w))) :=
      ((projectiveChart 1 0).left_inv hp).symm
    _ = (projectiveChart 1 0).symm
          ![reverseMobius (halfSpinMatrix (q : ℍ)) w] := by
      congr 1
      funext i
      fin_cases i
      exact secondSpinorPoint_reverse_action_ratio q w hden
    _ = affineSpinorPoint _ := by
      rw [affineSpinorPoint_eq_projectiveChart]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseMixedPoint
