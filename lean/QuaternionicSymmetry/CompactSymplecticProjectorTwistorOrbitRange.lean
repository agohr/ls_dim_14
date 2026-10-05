import QuaternionicSymmetry.CompactSymplecticProjectorTwistorProjection
import QuaternionicSymmetry.CompactSymplecticProjectorCarrierConnected
import QuaternionicSymmetry.CompactSymplecticProjectorColumnUnit

/-! The projectivized paired-column map lands in the actual compact
symplectic projector orbit, by concrete unit-column normalization. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorOrbitRange

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorTwistorNormalized
open CompactSymplecticProjectorTwistorScaleLaw
open CompactSymplecticProjectorTwistorProjection
open CompactSymplecticProjectorCarrierConnected
open CompactSymplecticProjectorColumnSphereMap
open CompactSymplecticProjectorColumnUnit
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev EV (n : ℕ) := EuclideanSpace ℂ (I n)

private def unitColumn (n : ℕ) (v : V n) (hv : v ≠ 0) :
    Metric.sphere (0 : EV n) 1 := by
  let w : EV n := (EuclideanSpace.equiv (I n) ℂ).symm v
  have hw : w ≠ 0 := by
    intro hz
    exact hv (by simpa [w] using congrArg (EuclideanSpace.equiv (I n) ℂ) hz)
  let t : ℂ := ((‖w‖ : ℝ) : ℂ)⁻¹
  refine ⟨t • w, mem_sphere_zero_iff_norm.mpr ?_⟩
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [norm_smul]
  simp [t, norm_inv, Complex.norm_real, abs_of_nonneg (norm_nonneg w),
    inv_mul_cancel₀ hn]

private theorem unitColumn_coord (n : ℕ) (v : V n) (hv : v ≠ 0) :
    (EuclideanSpace.equiv (I n) ℂ) (unitColumn n v hv).1 =
      (((‖(EuclideanSpace.equiv (I n) ℂ).symm v‖ : ℝ) : ℂ)⁻¹) • v := by
  change (EuclideanSpace.equiv (I n) ℂ)
    (((‖(EuclideanSpace.equiv (I n) ℂ).symm v‖ : ℝ) : ℂ)⁻¹ •
      (EuclideanSpace.equiv (I n) ℂ).symm v) = _
  rw [map_smul]
  change _ • WithLp.ofLp (WithLp.toLp 2 v) = _
  rw [WithLp.ofLp_toLp]

private theorem columnNormSq_eq_norm_sq (n : ℕ) (v : V n) :
    columnNormSq n v =
      (((‖(EuclideanSpace.equiv (I n) ℂ).symm v‖ : ℝ) ^ 2 : ℝ) : ℂ) := by
  let w : EV n := (EuclideanSpace.equiv (I n) ℂ).symm v
  have h := column_dot_self_eq_inner n w
  rw [inner_self_eq_norm_sq_to_K] at h
  simpa [columnNormSq, w] using h

theorem normalizedProjector_mem_orbit (n : ℕ) (v : V n) (hv : v ≠ 0) :
    normalizedProjector n v ∈ projectorOrbit n := by
  let w : EV n := (EuclideanSpace.equiv (I n) ℂ).symm v
  have hn : ‖w‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro hz
    exact hv (by simpa [w] using congrArg (EuclideanSpace.equiv (I n) ℂ) hz)
  let t : ℂ := ((‖w‖ : ℝ) : ℂ)⁻¹
  have ht : star t * t = (columnNormSq n v)⁻¹ := by
    rw [columnNormSq_eq_norm_sq]
    dsimp [t, w]
    simp [pow_two, mul_inv_rev, mul_comm]
  have heq : normalizedProjector n v =
      sphereColumnProjector n (unitColumn n v hv) := by
    rw [sphereColumnProjector, unitColumn_coord, columnProjector_smul]
    change (columnNormSq n v)⁻¹ • columnProjector n v =
      (star t * t) • columnProjector n v
    rw [ht]
  rw [heq]
  exact sphereColumnProjector_mem_orbit n (unitColumn n v hv)

theorem projectiveProjector_mem_orbit (n : ℕ) (p : ℙ ℂ (V n)) :
    projectiveProjector n p ∈ projectorOrbit n := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [projectiveProjector_mk]
    exact normalizedProjector_mem_orbit n v hv

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorOrbitRange
