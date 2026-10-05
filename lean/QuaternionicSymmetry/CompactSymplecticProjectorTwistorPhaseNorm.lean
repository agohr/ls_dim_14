import QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberSpan
import QuaternionicSymmetry.CompactSymplecticProjectorColumnTrace

/-! General (not necessarily unit) quaternionic phase law and its exact
norm factor. It supplies the reverse implication in the CP¹ fiber formula. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorPhaseNorm

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnPhase
open CompactSymplecticProjectorColumnTrace
open CompactSymplecticProjectorTwistorNormalized

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

theorem columnProjector_phaseRotate_general (n : ℕ)
    (a b : ℂ) (v : I n → ℂ) :
    columnProjector n (phaseRotate n a b v) =
      (star a * a + star b * b) • columnProjector n v := by
  ext i j
  unfold columnProjector
  rw [pairedColumn_phaseRotate]
  simp only [phaseRotate, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    Matrix.smul_apply, smul_eq_mul, star_add, star_sub, star_mul, star_star]
  ring

theorem columnNormSq_phaseRotate (n : ℕ)
    (a b : ℂ) (v : I n → ℂ) :
    columnNormSq n (phaseRotate n a b v) =
      (star a * a + star b * b) * columnNormSq n v := by
  have h := congrArg Matrix.trace (columnProjector_phaseRotate_general n a b v)
  rw [columnProjector_trace, Matrix.trace_smul, columnProjector_trace] at h
  change 2 * columnNormSq n (phaseRotate n a b v) =
    (star a * a + star b * b) * (2 * columnNormSq n v) at h
  linear_combination (1 / 2 : ℂ) * h

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorPhaseNorm
