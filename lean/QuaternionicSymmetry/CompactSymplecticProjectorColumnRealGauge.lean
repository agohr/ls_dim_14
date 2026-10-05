import QuaternionicSymmetry.CompactSymplecticProjectorColumnPhaseUnit

/-! Every unit quaternionic line has a unit complex representative whose
first paired coordinates are `(r,0)` for a real nonnegative `r`, while its
concrete rank-two projector is unchanged. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnRealGauge

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnPhase
open CompactSymplecticProjectorColumnPhaseNormalize
open CompactSymplecticProjectorColumnPhaseUnit
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := EuclideanSpace ℂ (I n)

theorem exists_real_first_pair_representative (n : ℕ)
    (v : Metric.sphere (0 : V n) 1) :
    ∃ (w : Metric.sphere (0 : V n) 1) (r : ℝ),
      0 ≤ r ∧ w.1 (Sum.inl 0) = (r : ℂ) ∧
      w.1 (Sum.inr 0) = 0 ∧
      columnProjector n ((EuclideanSpace.equiv (I n) ℂ) w.1) =
        columnProjector n ((EuclideanSpace.equiv (I n) ℂ) v.1) := by
  let A := v.1 (Sum.inl (0 : Fin (n + 1)))
  let B := v.1 (Sum.inr (0 : Fin (n + 1)))
  obtain ⟨a, b, r, hr, hab, hfirst, hsecond⟩ :=
    exists_unit_phase_first_pair_real A B
  let w := phaseRotateSphere n a b hab v
  refine ⟨w, r, hr, ?_, ?_, ?_⟩
  · simpa [w, phaseRotateSphere, phaseRotate, pairedColumn, A, B] using hfirst
  · simpa [w, phaseRotateSphere, phaseRotate, pairedColumn, A, B] using hsecond
  · simpa [w, phaseRotateSphere] using
      (columnProjector_phaseRotate n a b
        ((EuclideanSpace.equiv (I n) ℂ) v.1) hab)

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnRealGauge
