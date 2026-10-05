import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredSecondPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusPoint

/-! The actual half-spin projective action from source `[1:z]` into
target `[w:1]` is a genuine projective-point equality; no overlap of the
two affine charts is required at source or target. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedMobiusPoint

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  ComplexProjectiveTopology

noncomputable section

theorem affineSpinorPoint_mixed_action_mem (q : unitary ℍ) (z : ℂ)
    (hden : mixedDen (halfSpinMatrix (q : ℍ)) z ≠ 0) :
    projectiveHalfSpin q (affineSpinorPoint z) ∈ affineDomain 1 1 := by
  unfold affineSpinorPoint
  rw [projectiveHalfSpin_mk]
  apply (mem_affineDomain_mk 1 1 _ _).2
  simpa [mixedDen, chartNum, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] using hden

theorem affineSpinorPoint_mixed_action_ratio (q : unitary ℍ) (z : ℂ)
    (hden : mixedDen (halfSpinMatrix (q : ℍ)) z ≠ 0) :
    (projectiveChart 1 1)
      (projectiveHalfSpin q (affineSpinorPoint z)) 0 =
        mixedMobius (halfSpinMatrix (q : ℍ)) z := by
  let G := halfSpinMatrix (q : ℍ)
  let v := G *ᵥ ![1,z]
  have hden' : v 1 ≠ 0 := by
    simpa [v, G, mixedDen, chartNum, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using hden
  have hv : v ≠ 0 := by
    intro h
    exact hden' (by simpa [v] using congrFun h 1)
  have hpoint : projectiveHalfSpin q (affineSpinorPoint z) =
      Projectivization.mk ℂ v hv := by
    unfold affineSpinorPoint
    rw [projectiveHalfSpin_mk]
    rfl
  have hp := affineSpinorPoint_mixed_action_mem q z hden
  rw [projectiveChart_apply 1 1 _ hp]
  change affineRatio 1 1
    ⟨projectiveHalfSpin q (affineSpinorPoint z), hp⟩ 0 = _
  have hsub :
      (⟨projectiveHalfSpin q (affineSpinorPoint z), hp⟩ :
        {p : Space 1 // p ∈ affineDomain 1 1}) =
      ⟨Projectivization.mk ℂ v hv,
        (mem_affineDomain_mk 1 1 v hv).2 hden'⟩ :=
    Subtype.ext hpoint
  rw [hsub, affineRatio_mk 1 1 0 v hv hden']
  simp [mixedMobius, mixedNum, mixedDen, chartNum, chartDen,
    v, G, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem projectiveHalfSpin_mixedPoint (q : unitary ℍ) (z : ℂ)
    (hden : mixedDen (halfSpinMatrix (q : ℍ)) z ≠ 0) :
    projectiveHalfSpin q (affineSpinorPoint z) =
      secondAffineSpinorPoint (mixedMobius (halfSpinMatrix (q : ℍ)) z) := by
  have hp : projectiveHalfSpin q (affineSpinorPoint z) ∈
      (projectiveChart 1 1).source := by
    simpa [projectiveChart_source] using
      affineSpinorPoint_mixed_action_mem q z hden
  calc
    projectiveHalfSpin q (affineSpinorPoint z) =
        (projectiveChart 1 1).symm
          ((projectiveChart 1 1)
            (projectiveHalfSpin q (affineSpinorPoint z))) :=
      ((projectiveChart 1 1).left_inv hp).symm
    _ = (projectiveChart 1 1).symm
          ![mixedMobius (halfSpinMatrix (q : ℍ)) z] := by
      congr 1
      funext i
      fin_cases i
      exact affineSpinorPoint_mixed_action_ratio q z hden
    _ = secondAffineSpinorPoint _ := rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedMobiusPoint
