import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedToAmbientContinuous
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientEquiv
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCompact
import QuaternionicSymmetry.FiniteComplexProjectiveHausdorff

/-! The exact moved-line bijection identifies the genuine compact
Sp-associated CP¹ quotient with ambient CP^{2n+1} topologically. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientHomeomorph

open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedAmbientEquiv
open CompactSymplecticProjectorAssociatedToAmbientContinuous
open CompactSymplecticProjectorStabilizerHopfAction
open FourDimensionalHalfSpinProjectiveCompact
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := CompactSymplecticProjectiveQuotient.firstPairStabilizer n

def associatedAmbientHomeomorph (n : ℕ) :
    AssociatedProjectiveFiber n ≃ₜ ℙ ℂ (V n) := by
  letI := projectiveFiberAction n
  letI : CompactSpace (AssociatedProjectiveFiber n) := Quotient.compactSpace
  letI : T2Space (ℙ ℂ (V n)) := FiniteComplexProjectiveHausdorff.t2Space (I n)
  let E := associatedAmbientEquiv n
  have hc : Continuous E := continuous_associatedToAmbient n
  exact E.toHomeomorphOfContinuousClosed hc hc.isClosedMap

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientHomeomorph
