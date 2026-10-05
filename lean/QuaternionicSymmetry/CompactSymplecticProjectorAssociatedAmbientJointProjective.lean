import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientJointVector
import QuaternionicSymmetry.ComplexProjectiveHausdorff

/-! Joint continuity of the concrete moved CP¹ point on the genuine
projective spinor, descended from unit-spinor representatives. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientJointProjective

open Topology
open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorAssociatedAmbientJointVector
open FourDimensionalHalfSpinProjective
open FourDimensionalHalfSpinProjectiveCompact

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev UnitSpinor := Metric.sphere (0 : Spinor) 1

private theorem unitProjective_pair_quotient (n : ℕ) :
    IsQuotientMap (fun p : G n × UnitSpinor => (p.1, unitProjective p.2)) := by
  letI : CompactSpace UnitSpinor := Metric.sphere.compactSpace _ _
  apply IsQuotientMap.of_surjective_continuous
  · rintro ⟨u,z⟩
    obtain ⟨v, rfl⟩ := unitProjective_surjective z
    exact ⟨(u,v), rfl⟩
  · exact continuous_fst.prodMk (unitProjective_continuous.comp continuous_snd)

theorem continuous_jointFiberProjective (n : ℕ) :
    Continuous (fun p : G n × ProjectiveSpinor =>
      fiberProjectiveLine n (firstColumnSphere n p.1) p.2) := by
  apply (unitProjective_pair_quotient n).continuous_iff.mpr
  exact continuous_jointFiberProjectiveUnit n

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientJointProjective
