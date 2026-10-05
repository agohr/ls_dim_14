import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral

/-! The finite complex unitary group is compact and carries an actual
normalized Haar probability measure for the projection moment argument. -/

namespace QuaternionicSymmetry.UnitaryHaarMeasure

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem isCompact_unitary : IsCompact (unitary (Matrix κ κ ℂ) : Set (Matrix κ κ ℂ)) := by
  apply (isCompact_closedBall (0 : Matrix κ κ ℂ) 1).of_isClosed_subset isClosed_unitary
  intro U hU
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entrywise_sup_norm_bound_of_unitary hU

instance compactSpace : CompactSpace (Matrix.unitaryGroup κ ℂ) :=
  isCompact_iff_compactSpace.mp isCompact_unitary

instance measurableSpace : MeasurableSpace (Matrix.unitaryGroup κ ℂ) :=
  borel (Matrix.unitaryGroup κ ℂ)

instance borelSpace : BorelSpace (Matrix.unitaryGroup κ ℂ) := ⟨rfl⟩

def probability : Measure (Matrix.unitaryGroup κ ℂ) :=
  Measure.haarMeasure ⊤

instance probability_isProbabilityMeasure :
    IsProbabilityMeasure (probability (κ := κ)) where
  measure_univ := Measure.haarMeasure_self

instance probability_isHaarMeasure : Measure.IsHaarMeasure (probability (κ := κ)) := by
  unfold probability
  infer_instance

instance probability_isMulRightInvariant :
    Measure.IsMulRightInvariant (probability (κ := κ)) where
  map_mul_right_eq_self U := by
    have h := Measure.haarMeasure_unique
      (Measure.map (fun g : Matrix.unitaryGroup κ ℂ => g * U) probability)
      (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup κ ℂ))
    simpa only [TopologicalSpace.PositiveCompacts.coe_top,
      Measure.map_apply (measurable_mul_const U) MeasurableSet.univ,
      Set.preimage_univ, measure_univ, one_smul] using h

instance probability_isInvInvariant :
    Measure.IsInvInvariant (probability (κ := κ)) where
  inv_eq_self := by
    have h := Measure.haarMeasure_unique (probability (κ := κ)).inv
      (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup κ ℂ))
    simpa only [TopologicalSpace.PositiveCompacts.coe_top,
      Measure.inv_apply, Set.inv_univ, measure_univ, one_smul] using h

theorem integral_mul_left (f : Matrix.unitaryGroup κ ℂ → ℝ)
    (U : Matrix.unitaryGroup κ ℂ) :
    (∫ g, f (U * g) ∂probability) = ∫ g, f g ∂probability :=
  integral_mul_left_eq_self f U

theorem integral_mul_right (f : Matrix.unitaryGroup κ ℂ → ℝ)
    (U : Matrix.unitaryGroup κ ℂ) :
    (∫ g, f (g * U) ∂probability) = ∫ g, f g ∂probability :=
  integral_mul_right_eq_self f U

theorem integral_inv (f : Matrix.unitaryGroup κ ℂ → ℝ) :
    (∫ g, f g⁻¹ ∂probability) = ∫ g, f g ∂probability :=
  integral_inv_eq_self f probability

end
end QuaternionicSymmetry.UnitaryHaarMeasure
