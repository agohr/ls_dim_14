import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientJointProjective
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedToAmbient

/-! The literal stabilizer-independent moved-line map from the associated
CP¹ quotient to ambient CP^{2n+1} is continuous in both actual quotient
topologies. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedToAmbientContinuous

open Topology
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedToAmbient
open CompactSymplecticProjectorAssociatedAmbientJointProjective
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorFirstColumnUnit
open FourDimensionalHalfSpinProjective
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := CompactSymplecticProjectiveQuotient.firstPairStabilizer n

theorem continuous_associatedToAmbient (n : ℕ) :
    Continuous (associatedToAmbient n : AssociatedProjectiveFiber n → ℙ ℂ (V n)) := by
  letI := projectiveFiberAction n
  let s := @MulAction.orbitRel (K n) (G n × ProjectiveSpinor) _
    (associatedAction n)
  have hquot : IsQuotientMap (@Quotient.mk' (G n × ProjectiveSpinor) s) :=
    isQuotientMap_quotient_mk'
  apply hquot.continuous_iff.mpr
  exact (continuous_jointFiberProjective n).congr (fun p => by
    exact (associatedToAmbient_mk n p.1 p.2).symm)

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedToAmbientContinuous
