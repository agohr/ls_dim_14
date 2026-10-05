import QuaternionicSymmetry.CompactSymplecticProjectorColumnTrace

/-! Quaternionic unit phase rotation preserves the Euclidean unit sphere,
deduced from the explicit trace identity and projector invariance. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnPhaseUnit

open Matrix CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnPhase
open CompactSymplecticProjectorColumnTrace
open CompactSymplecticProjectorColumnUnit
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

theorem phaseRotate_dot_self (n : ℕ) (a b : ℂ) (v : I n → ℂ)
    (hab : star a * a + star b * b = 1) :
    (fun i => star (phaseRotate n a b v i)) ⬝ᵥ phaseRotate n a b v =
      (fun i => star (v i)) ⬝ᵥ v := by
  have h := congrArg Matrix.trace (columnProjector_phaseRotate n a b v hab)
  rw [columnProjector_trace, columnProjector_trace] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

def phaseRotateSphere (n : ℕ) (a b : ℂ)
    (hab : star a * a + star b * b = 1)
    (v : Metric.sphere (0 : EuclideanSpace ℂ (I n)) 1) :
    Metric.sphere (0 : EuclideanSpace ℂ (I n)) 1 := by
  let w : EuclideanSpace ℂ (I n) :=
    (EuclideanSpace.equiv (I n) ℂ).symm
      (phaseRotate n a b ((EuclideanSpace.equiv (I n) ℂ) v.1))
  have hwinner : inner ℂ w w = 1 := by
    rw [← CompactSymplecticProjectorColumnUnit.column_dot_self_eq_inner]
    exact (phaseRotate_dot_self n a b _ hab).trans (unit_column_dot_self n v)
  have hwnorm : ‖w‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hwinner]
    norm_num
  exact ⟨w, mem_sphere_zero_iff_norm.mpr hwnorm⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnPhaseUnit
