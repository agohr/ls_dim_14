import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedBase
import QuaternionicSymmetry.CompactSymplecticProjectorTwistorAssociatedDescentLinear
import QuaternionicSymmetry.CompactSymplecticProjectorTwistorGroupFiberBase

/-! The actual associated CP¹ bundle maps to the independently constructed
ambient CP^{2n+1} twistor projection. The map is defined on representatives
by the concrete moved complex line, and its stabilizer-independence follows
from the checked matrix first-block action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedToAmbient

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedBase
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorTwistorAssociatedDescentLinear
open CompactSymplecticProjectorTwistorGroupFiberBase
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticProjectorFirstBlockHopfAction
open CompactSymplecticStabilizerBlockPair
open FourDimensionalHalfSpinProjective
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := firstPairStabilizer n

theorem movedFiber_stabilizer_independent (n : ℕ) (u : G n)
    (k : K n) (p : ProjectiveSpinor) :
    letI := projectiveFiberAction n
    fiberProjectiveLine n (firstColumnSphere n (u * (k⁻¹ : G n)))
        (k • p) = fiberProjectiveLine n (firstColumnSphere n u) p := by
  letI := projectiveFiberAction n
  induction p using Projectivization.ind with
  | h z hz =>
    change fiberProjectiveLine n (firstColumnSphere n (u * (k⁻¹ : G n)))
      (projectiveHalfSpin
        (CompactSymplecticProjectorFirstBlockUnitQuaternion.firstBlockUnitQuaternion
          (blockPair n k).1)
        (Projectivization.mk ℂ z hz)) = _
    rw [firstBlock_projective_action_mk (blockPair n k).1 z hz]
    simp only [fiberProjectiveLine, Projectivization.map_mk]
    congr 1
    exact fiberLineMap_stabilizer_independent n u k z

def associatedToAmbient (n : ℕ) :
    AssociatedProjectiveFiber n → ℙ ℂ (V n) := by
  letI := projectiveFiberAction n
  refine Quotient.lift (fun z : G n × ProjectiveSpinor =>
    fiberProjectiveLine n (firstColumnSphere n z.1) z.2) ?_
  intro a b hab
  change ∃ k : K n, (associatedAction n).smul k b = a at hab
  rcases hab with ⟨k, hk⟩
  rw [← hk]
  exact movedFiber_stabilizer_independent n b.1 k b.2

@[simp] theorem associatedToAmbient_mk (n : ℕ) (u : G n)
    (p : ProjectiveSpinor) :
    associatedToAmbient n (⟦(u,p)⟧ : AssociatedProjectiveFiber n) =
      fiberProjectiveLine n (firstColumnSphere n u) p := rfl

theorem associatedToAmbient_base (n : ℕ)
    (z : AssociatedProjectiveFiber n) :
    CompactSymplecticProjectorTwistorCarrierMap.twistorToCarrier n
      (associatedToAmbient n z) = projectiveBase n z := by
  induction z using Quotient.inductionOn with
  | _ z => exact twistorToCarrier_fiberLine_at_group n z.1 z.2

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedToAmbient
