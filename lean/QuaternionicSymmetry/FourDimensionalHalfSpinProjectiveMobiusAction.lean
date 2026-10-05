import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseComplex
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGaugeChart
import QuaternionicSymmetry.ComplexProjectiveAffineTopology

/-! The unit-quaternion projective half-spin action is literally the
Möbius function used in the connection gauge law, in the true CP¹
affine-ratio chart wherever its denominator is nonzero. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusAction

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinProjectiveGaugeChart
  ComplexProjectiveTopology

noncomputable section

def affineSpinorPoint (z : ℂ) : ProjectiveSpinor :=
  Projectivization.mk ℂ ![1,z] (by
    intro h
    have h0 := congrFun h 0
    simp at h0)

theorem affineSpinorPoint_action_mem (q : unitary ℍ) (z : ℂ)
    (hden : chartDen (halfSpinMatrix (q : ℍ)) z ≠ 0) :
    projectiveHalfSpin q (affineSpinorPoint z) ∈ affineDomain 1 0 := by
  unfold affineSpinorPoint
  rw [projectiveHalfSpin_mk]
  apply (mem_affineDomain_mk 1 0 _ _).2
  change (halfSpinMatrix (q : ℍ) *ᵥ ![1,z]) 0 ≠ 0
  rwa [chartDen_eq]

theorem affineSpinorPoint_action_ratio (q : unitary ℍ) (z : ℂ)
    (hden : chartDen (halfSpinMatrix (q : ℍ)) z ≠ 0) :
    affineRatio 1 0
      ⟨projectiveHalfSpin q (affineSpinorPoint z),
        affineSpinorPoint_action_mem q z hden⟩ 1 =
      mobius (halfSpinMatrix (q : ℍ)) z := by
  let v := halfSpinMatrix (q : ℍ) *ᵥ ![1,z]
  have hden' : (halfSpinMatrix (q : ℍ) *ᵥ ![1,z]) 0 ≠ 0 := by
    rwa [chartDen_eq]
  have hv : v ≠ 0 := by
    intro h
    exact hden' (by simpa [v] using congrFun h 0)
  have hpoint : projectiveHalfSpin q (affineSpinorPoint z) =
      Projectivization.mk ℂ v hv := by
    unfold affineSpinorPoint
    rw [projectiveHalfSpin_mk]
    rfl
  have hsub :
      (⟨projectiveHalfSpin q (affineSpinorPoint z),
        affineSpinorPoint_action_mem q z hden⟩ :
          {p : Space 1 // p ∈ affineDomain 1 0}) =
      ⟨Projectivization.mk ℂ v hv,
        (mem_affineDomain_mk 1 0 v hv).2 hden'⟩ :=
    Subtype.ext hpoint
  rw [hsub, affineRatio_mk 1 0 1 v hv hden']
  simp only [v, mobius, ← chartNum_eq, ← chartDen_eq]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusAction
