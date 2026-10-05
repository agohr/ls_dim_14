import QuaternionicSymmetry.CompactSymplecticProjectorTwistorOrbitRange

/-! The concrete complex-projective-to-quaternionic-projective map, obtained
by the proved rank-two projector orbit homeomorphism. It is onto and folds
the fixed-point-free quaternionic antipodal pair into a common base point.
No holomorphicity/contact or smooth twistor identification is claimed. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorCarrierMap

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorTwistorAntipodal
open CompactSymplecticProjectorTwistorNormalized
open CompactSymplecticProjectorTwistorProjection
open CompactSymplecticProjectorTwistorOrbitRange
open CompactSymplecticProjectorCarrierConnected
open CompactSymplecticProjectorColumnSphereMap
open CompactSymplecticProjectorColumnUnit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectiveQuotient
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev EV (n : ℕ) := EuclideanSpace ℂ (I n)

def twistorToCarrier (n : ℕ) : ℙ ℂ (V n) → ProjectiveCarrier n :=
  fun p => (carrierHomeomorphProjectorOrbit n).symm
    ⟨projectiveProjector n p, projectiveProjector_mem_orbit n p⟩

theorem carrier_projector_twistorToCarrier (n : ℕ) (p : ℙ ℂ (V n)) :
    quotientOrbitProjector n (twistorToCarrier n p) =
      projectiveProjector n p := by
  change ((carrierHomeomorphProjectorOrbit n) (twistorToCarrier n p)).1 = _
  simp [twistorToCarrier]

theorem twistorToCarrier_antipodal (n : ℕ) (p : ℙ ℂ (V n)) :
    twistorToCarrier n (antipodal n p) = twistorToCarrier n p := by
  apply (carrierHomeomorphProjectorOrbit n).injective
  apply Subtype.ext
  simpa [twistorToCarrier] using projectiveProjector_antipodal n p

private theorem normalizedProjector_unit (n : ℕ)
    (w : Metric.sphere (0 : EV n) 1) :
    normalizedProjector n ((EuclideanSpace.equiv (I n) ℂ) w.1) =
      sphereColumnProjector n w := by
  have hdot := unit_column_dot_self n w
  have hnorm : columnNormSq n ((EuclideanSpace.equiv (I n) ℂ) w.1) = 1 := by
    simpa [columnNormSq] using hdot
  simp [normalizedProjector, hnorm, sphereColumnProjector]

theorem twistorToCarrier_surjective (n : ℕ) :
    Function.Surjective (twistorToCarrier n) := by
  intro x
  obtain ⟨w, hw⟩ := (carrierHomeomorphProjectorOrbit n).symm.surjective x
  obtain ⟨v, hv⟩ := sphereToOrbit_surjective n w
  let c : V n := (EuclideanSpace.equiv (I n) ℂ) v.1
  have hc : c ≠ 0 := by
    intro hz
    have hzv : v.1 = 0 := (EuclideanSpace.equiv (I n) ℂ).injective hz
    have hn := mem_sphere_zero_iff_norm.mp v.2
    simp [hzv] at hn
  refine ⟨Projectivization.mk ℂ c hc, ?_⟩
  rw [← hw, ← hv]
  change (carrierHomeomorphProjectorOrbit n).symm
    ⟨projectiveProjector n (Projectivization.mk ℂ c hc),
      projectiveProjector_mem_orbit n _⟩ =
    (carrierHomeomorphProjectorOrbit n).symm (sphereToOrbit n v)
  congr 1
  apply Subtype.ext
  simpa [c, sphereToOrbit, projectiveProjector_mk] using
    normalizedProjector_unit n v

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorCarrierMap
