import QuaternionicSymmetry.CompactSymplecticProjectorTwistorCarrierMap
import QuaternionicSymmetry.ComplexProjectiveTopology

/-! Continuity of the concrete complex-projective-to-quaternionic-projective
twistor projection under the standard quotient topology. This still does not
identify the complex/contact twistor atlas of the Levi-Civita connection. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorContinuous

open CompactSymplecticProjectorColumnContinuity
open CompactSymplecticProjectorTwistorNormalized
open CompactSymplecticProjectorTwistorProjection
open CompactSymplecticProjectorTwistorOrbitRange
open CompactSymplecticProjectorTwistorCarrierMap
open CompactSymplecticProjectorOrbitQuotient
open ComplexProjectiveTopology
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ

theorem continuous_columnNormSq (n : ℕ) :
    Continuous (columnNormSq n : V n → ℂ) := by
  classical
  change Continuous (fun v : V n => (star v) ⬝ᵥ v)
  simp only [dotProduct]
  fun_prop

theorem continuous_normalizedProjector_nonzero (n : ℕ) :
    Continuous (fun v : {v : V n // v ≠ 0} => normalizedProjector n v.1) := by
  have hn : Continuous (fun v : {v : V n // v ≠ 0} => columnNormSq n v.1) :=
    (continuous_columnNormSq n).comp continuous_subtype_val
  have hn0 : ∀ v : {v : V n // v ≠ 0}, columnNormSq n v.1 ≠ 0 :=
    fun v => columnNormSq_ne_zero n v.2
  have hp : Continuous (fun v : {v : V n // v ≠ 0} =>
      CompactSymplecticProjectorFirstColumn.columnProjector n v.1) :=
    (continuous_columnProjector n).comp continuous_subtype_val
  exact (hn.inv₀ hn0).smul hp

theorem continuous_projectiveProjector (n : ℕ) :
    Continuous (projectiveProjector n) := by
  apply (isQuotientMap_quotient_mk' : Topology.IsQuotientMap
    (Projectivization.mk' ℂ : {v : V n // v ≠ 0} → ℙ ℂ (V n))).continuous_iff.mpr
  change Continuous (fun v : {v : V n // v ≠ 0} => normalizedProjector n v.1)
  exact continuous_normalizedProjector_nonzero n

theorem continuous_twistorToCarrier (n : ℕ) :
    Continuous (twistorToCarrier n) := by
  exact (carrierHomeomorphProjectorOrbit n).symm.continuous.comp
    ((continuous_projectiveProjector n).subtype_mk _)

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorContinuous
