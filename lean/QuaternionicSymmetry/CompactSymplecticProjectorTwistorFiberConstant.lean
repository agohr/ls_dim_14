import QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberLine

/-! Every point on the concretely embedded complex projective line over a
unit quaternionic column has the same normalized projector and hence the
same point of the actual HP quotient. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberConstant

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnPhase
open CompactSymplecticProjectorTwistorNormalized
open CompactSymplecticProjectorTwistorPhaseNorm
open CompactSymplecticProjectorTwistorProjection
open CompactSymplecticProjectorTwistorCarrierMap
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorOrbitQuotient
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev EV (n : ℕ) := EuclideanSpace ℂ (I n)

theorem normalizedProjector_phaseRotate (n : ℕ) (a b : ℂ) (v : V n)
    (hv : phaseRotate n a b v ≠ 0) :
    normalizedProjector n (phaseRotate n a b v) = normalizedProjector n v := by
  let c := star a * a + star b * b
  have hc : c ≠ 0 := by
    intro hz
    have hn := columnNormSq_phaseRotate n a b v
    change columnNormSq n (phaseRotate n a b v) = c * columnNormSq n v at hn
    rw [hz, zero_mul] at hn
    exact columnNormSq_ne_zero n hv hn
  simp only [normalizedProjector, columnNormSq_phaseRotate,
    columnProjector_phaseRotate_general, smul_smul]
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]

theorem fiberProjectiveLine_constant (n : ℕ)
    (w : Metric.sphere (0 : EV n) 1)
    (z : ℙ ℂ (Fin 2 → ℂ)) :
    twistorToCarrier n (fiberProjectiveLine n w z) =
      twistorToCarrier n
        (Projectivization.mk ℂ ((EuclideanSpace.equiv (I n) ℂ) w.1)
          (by
            intro hz
            have hw : w.1 = 0 := (EuclideanSpace.equiv (I n) ℂ).injective hz
            have hn := mem_sphere_zero_iff_norm.mp w.2
            simp [hw] at hn)) := by
  induction z using Projectivization.ind with
  | h z hz =>
    have hproj : projectiveProjector n
        (fiberProjectiveLine n w (Projectivization.mk ℂ z hz)) =
        projectiveProjector n
          (Projectivization.mk ℂ ((EuclideanSpace.equiv (I n) ℂ) w.1) (by
            intro hzero
            have hw : w.1 = 0 := (EuclideanSpace.equiv (I n) ℂ).injective hzero
            have hn := mem_sphere_zero_iff_norm.mp w.2
            simp [hw] at hn)) := by
      simp only [fiberProjectiveLine, Projectivization.map_mk,
        projectiveProjector_mk]
      change normalizedProjector n
        (phaseRotate n (z 0) (z 1) ((EuclideanSpace.equiv (I n) ℂ) w.1)) = _
      apply normalizedProjector_phaseRotate
      simpa [fiberLineMap, phaseRotate] using (fiberLineMap_injective n w).ne hz
    apply (carrierHomeomorphProjectorOrbit n).injective
    apply Subtype.ext
    simpa [twistorToCarrier] using hproj

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberConstant
