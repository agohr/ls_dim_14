import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusRealTangent
import QuaternionicSymmetry.ComplexProjectiveAffineEuclidean

/-! On the standard nonzero-denominator affine patch, the actual
projective half-spin action sends the point `[1:z]` to `[1:mobius(q,z)]`,
as equality of genuine projective points, not just equality of ratios. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusPoint

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinProjectiveMobiusAction
  ComplexProjectiveTopology

noncomputable section

theorem affineSpinorPoint_mem (z : ℂ) :
    affineSpinorPoint z ∈ affineDomain 1 0 := by
  unfold affineSpinorPoint
  apply (mem_affineDomain_mk 1 0 _ _).2
  simp

theorem affineSpinorPoint_ratio (z : ℂ) :
    affineRatio 1 0 ⟨affineSpinorPoint z,
      affineSpinorPoint_mem z⟩ 1 = z := by
  unfold affineSpinorPoint
  rw [affineRatio_mk 1 0 1 _ _ (by simp)]
  simp

theorem projectiveHalfSpin_affinePoint (q : unitary ℍ) (z : ℂ)
    (hden : chartDen (halfSpinMatrix (q : ℍ)) z ≠ 0) :
    projectiveHalfSpin q (affineSpinorPoint z) =
      affineSpinorPoint (mobius (halfSpinMatrix (q : ℍ)) z) := by
  let w := mobius (halfSpinMatrix (q : ℍ)) z
  have hcoord :
      (affineEuclideanHomeomorph 1 0)
        ⟨projectiveHalfSpin q (affineSpinorPoint z),
          affineSpinorPoint_action_mem q z hden⟩ =
      (affineEuclideanHomeomorph 1 0)
        ⟨affineSpinorPoint w, affineSpinorPoint_mem w⟩ := by
    funext k
    fin_cases k
    change affineRatio 1 0
        ⟨projectiveHalfSpin q (affineSpinorPoint z),
          affineSpinorPoint_action_mem q z hden⟩ 1 =
      affineRatio 1 0 ⟨affineSpinorPoint w,
        affineSpinorPoint_mem w⟩ 1
    rw [affineSpinorPoint_action_ratio q z hden, affineSpinorPoint_ratio]
  exact congrArg Subtype.val
    ((affineEuclideanHomeomorph 1 0).injective hcoord)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusPoint
