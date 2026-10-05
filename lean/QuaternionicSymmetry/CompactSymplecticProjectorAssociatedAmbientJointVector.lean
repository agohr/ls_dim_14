import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedToAmbient
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCompact

/-! The actual ambient complex vector representing a moved CP¹ fiber point
depends jointly continuously on the symplectic group element and spinor. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientJointVector

open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticProjectorColumnContinuity
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorColumnPhase
open FourDimensionalHalfSpinProjective
open FourDimensionalHalfSpinProjectiveCompact
open ComplexProjectiveTopology
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev EV (n : ℕ) := EuclideanSpace ℂ (I n)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev UnitSpinor := Metric.sphere (0 : Spinor) 1

theorem continuous_jointFiberVector (n : ℕ) :
    Continuous (fun p : G n × UnitSpinor =>
      fiberLineMap n (firstColumnSphere n p.1) p.2.1) := by
  have hw : Continuous (fun p : G n × UnitSpinor =>
      ((EuclideanSpace.equiv (I n) ℂ) (firstColumnSphere n p.1).1 : V n)) :=
    (EuclideanSpace.equiv (I n) ℂ).continuous.comp
      (continuous_subtype_val.comp ((continuous_firstColumnSphere n).comp continuous_fst))
  change Continuous (fun p : G n × UnitSpinor =>
    phaseRotate n (p.2.1 0) (p.2.1 1)
      ((EuclideanSpace.equiv (I n) ℂ) (firstColumnSphere n p.1).1))
  unfold phaseRotate
  have h0 : Continuous (fun p : G n × UnitSpinor => p.2.1 0) :=
    (continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd)
  have h1 : Continuous (fun p : G n × UnitSpinor => p.2.1 1) :=
    (continuous_apply 1).comp (continuous_subtype_val.comp continuous_snd)
  exact h0.smul hw |>.add (h1.smul (by
    change Continuous (fun p : G n × UnitSpinor =>
      CompactSymplecticProjectorFirstColumn.pairedColumn n
        ((EuclideanSpace.equiv (I n) ℂ) (firstColumnSphere n p.1).1))
    exact (continuous_pairedColumn n).comp hw))

private theorem unitSpinor_ne_zero (z : UnitSpinor) : (z.1 : Spinor) ≠ 0 := by
  have hz : ‖(z.1 : Spinor)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.2
  intro h
  rw [h, norm_zero] at hz
  norm_num at hz

theorem continuous_jointFiberProjectiveUnit (n : ℕ) :
    Continuous (fun p : G n × UnitSpinor =>
      fiberProjectiveLine n (firstColumnSphere n p.1) (unitProjective p.2)) := by
  have hvec := continuous_jointFiberVector n
  have hsub : Continuous (fun p : G n × UnitSpinor =>
      (⟨fiberLineMap n (firstColumnSphere n p.1) p.2.1,
        by
          simpa using (fiberLineMap_injective n (firstColumnSphere n p.1)).ne
            (unitSpinor_ne_zero p.2)⟩ : {v : V n // v ≠ 0})) :=
    hvec.subtype_mk _
  have hmk : Continuous
      (Projectivization.mk' ℂ : {v : V n // v ≠ 0} → ℙ ℂ (V n)) :=
    continuous_quotient_mk'
  convert hmk.comp hsub using 1

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientJointVector
