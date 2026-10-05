import QuaternionicSymmetry.CompactSymplecticProjectorTwistorAntipodal

/-! The concrete projective antipodal pair lies in one quaternionic line:
the rank-two Hermitian projector obtained from `v` is unchanged by replacing
`v` with its quaternionic mate. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberLaw

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnPhase
open CompactSymplecticProjectorTwistorAntipodal

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

theorem columnProjector_pairedColumn (n : ℕ) (v : I n → ℂ) :
    columnProjector n (pairedColumn n v) = columnProjector n v := by
  have h := columnProjector_phaseRotate n 0 1 v (by norm_num)
  simpa [phaseRotate] using h

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberLaw
