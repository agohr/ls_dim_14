import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedHopfEquiv

/-! The complex-orientation-corrected Hopf map is likewise a genuine
equivalence of associated total spaces over the actual projector quotient. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedEquiv

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedBase
open CompactSymplecticProjectorAssociatedCorrectedHopf
open CompactSymplecticProjectorAssociatedHopfEquiv
open CompactSymplecticProjectorStabilizerHopfAction
open FourDimensionalHalfSpinAntipodalVerticalSign
open ManifoldTwistorSphereBundle

noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

theorem antipodalCoefficient_involutive (a : coefficientSphere) :
    antipodalCoefficient (antipodalCoefficient a) = a := by
  apply Subtype.ext
  simp [antipodalCoefficient]

theorem associatedAntipodal_involutive (n : ℕ)
    (S : QuaternionicStructure E) (z : AssociatedSphereFiber n S) :
    associatedAntipodal n S (associatedAntipodal n S z) = z := by
  induction z using Quotient.inductionOn with
  | _ z =>
    change (⟦(z.1, antipodalCoefficient (antipodalCoefficient z.2))⟧ :
      AssociatedSphereFiber n S) = ⟦z⟧
    rw [antipodalCoefficient_involutive]

def associatedAntipodalEquiv (n : ℕ) (S : QuaternionicStructure E) :
    AssociatedSphereFiber n S ≃ AssociatedSphereFiber n S where
  toFun := associatedAntipodal n S
  invFun := associatedAntipodal n S
  left_inv := associatedAntipodal_involutive n S
  right_inv := associatedAntipodal_involutive n S

def associatedCorrectedHopfEquiv (n : ℕ) (S : QuaternionicStructure E) :
    AssociatedProjectiveFiber n ≃ AssociatedSphereFiber n S :=
  (associatedHopfEquiv n S).trans (associatedAntipodalEquiv n S)

theorem associatedCorrectedHopfEquiv_apply (n : ℕ)
    (S : QuaternionicStructure E) (z : AssociatedProjectiveFiber n) :
    associatedCorrectedHopfEquiv n S z = associatedCorrectedHopf n S z := rfl

theorem associatedCorrectedHopfEquiv_base (n : ℕ)
    (S : QuaternionicStructure E) (z : AssociatedProjectiveFiber n) :
    sphereBase n S (associatedCorrectedHopfEquiv n S z) =
      projectiveBase n z :=
  associatedCorrectedHopf_base n S z

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedEquiv
