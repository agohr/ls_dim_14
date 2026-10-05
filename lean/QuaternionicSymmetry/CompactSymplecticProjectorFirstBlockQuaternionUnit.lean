import QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionAction

/-! The quaternion read from an actual first-block compact-symplectic
matrix is nonzero, using its checked unitary matrix property. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockQuaternionUnit

open Matrix
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticStabilizerBlockPair
open scoped Quaternion

theorem firstBlockQuaternion_ne_zero (A : FirstBlockGroup) :
    firstBlockQuaternion A ≠ 0 := by
  intro hq
  have haRe : (A.1.1 0 0).re = 0 := by
    have h := congrArg (fun x : ℍ => x.re) hq
    simpa [firstBlockQuaternion] using h
  have haIm : (A.1.1 0 0).im = 0 := by
    have h := congrArg (fun x : ℍ => x.imI) hq
    simpa [firstBlockQuaternion] using h
  have hbRe : (A.1.1 0 1).re = 0 := by
    have h := congrArg (fun x : ℍ => x.imJ) hq
    simpa [firstBlockQuaternion] using neg_eq_zero.mp h
  have hbIm : (A.1.1 0 1).im = 0 := by
    have h := congrArg (fun x : ℍ => x.imK) hq
    simpa [firstBlockQuaternion] using neg_eq_zero.mp h
  have ha : (A.1.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 :=
    Complex.ext haRe haIm
  have hb : (A.1.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 :=
    Complex.ext hbRe hbIm
  have hunit := (Matrix.mem_unitaryGroup_iff).mp A.1.property
  rw [Matrix.star_eq_conjTranspose] at hunit
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hunit
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb] at h

end QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockQuaternionUnit
