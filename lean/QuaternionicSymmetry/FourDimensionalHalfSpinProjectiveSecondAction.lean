import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondMobius
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusPoint

/-! The actual projectivized half-spin matrix action has the certified
second-affine Möbius ratio, including the south pole, whenever its second
homogeneous coordinate is nonzero. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondAction

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinProjectiveSecondMobius
  ComplexProjectiveTopology

noncomputable section

theorem secondAffineSpinorPoint_action_mem (q : unitary ℍ) (w : ℂ)
    (hden : secondDen (halfSpinMatrix (q : ℍ)) w ≠ 0) :
    projectiveHalfSpin q (secondAffineSpinorPoint w) ∈ affineDomain 1 1 := by
  rw [secondAffineSpinorPoint_mk, projectiveHalfSpin_mk]
  apply (mem_affineDomain_mk 1 1 _ _).2
  simpa [secondDen, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    using hden

theorem secondAffineSpinorPoint_action_ratio (q : unitary ℍ) (w : ℂ)
    (hden : secondDen (halfSpinMatrix (q : ℍ)) w ≠ 0) :
    (projectiveChart 1 1)
      (projectiveHalfSpin q (secondAffineSpinorPoint w)) 0 =
        secondMobius (halfSpinMatrix (q : ℍ)) w := by
  let G := halfSpinMatrix (q : ℍ)
  let v := G *ᵥ ![w,1]
  have hden' : v 1 ≠ 0 := by
    simpa [v, G, secondDen, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using hden
  have hv : v ≠ 0 := by
    intro h
    exact hden' (by simpa [v] using congrFun h 1)
  have hpoint : projectiveHalfSpin q (secondAffineSpinorPoint w) =
      Projectivization.mk ℂ v hv := by
    rw [secondAffineSpinorPoint_mk, projectiveHalfSpin_mk]
    rfl
  have hp := secondAffineSpinorPoint_action_mem q w hden
  rw [projectiveChart_apply 1 1 _ hp]
  change affineRatio 1 1
    ⟨projectiveHalfSpin q (secondAffineSpinorPoint w), hp⟩ 0 = _
  have hsub :
      (⟨projectiveHalfSpin q (secondAffineSpinorPoint w), hp⟩ :
        {p : Space 1 // p ∈ affineDomain 1 1}) =
      ⟨Projectivization.mk ℂ v hv,
        (mem_affineDomain_mk 1 1 v hv).2 hden'⟩ :=
    Subtype.ext hpoint
  rw [hsub, affineRatio_mk 1 1 0 v hv hden']
  simp [secondMobius, secondNum, secondDen, v, G,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondAction
