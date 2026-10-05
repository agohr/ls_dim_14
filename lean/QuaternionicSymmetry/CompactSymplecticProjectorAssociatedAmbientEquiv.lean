import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientInjective
import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedEquiv

/-! Set-level, base-preserving identification of the checked ambient complex
projective twistor candidate with the genuine Sp(n+1)-associated CP¹ bundle,
then with its correctly oriented associated coefficient-sphere bundle. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientEquiv

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedBase
open CompactSymplecticProjectorAssociatedToAmbient
open CompactSymplecticProjectorAssociatedAmbientSurjection
open CompactSymplecticProjectorAssociatedAmbientInjective
open CompactSymplecticProjectorAssociatedCorrectedEquiv
open CompactSymplecticProjectorTwistorCarrierMap
open ManifoldTwistorSphereBundle
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ

def associatedAmbientEquiv (n : ℕ) :
    AssociatedProjectiveFiber n ≃ ℙ ℂ (V n) :=
  Equiv.ofBijective (associatedToAmbient n)
    ⟨associatedToAmbient_injective n, associatedToAmbient_surjective n⟩

theorem associatedAmbientEquiv_base (n : ℕ)
    (z : AssociatedProjectiveFiber n) :
    twistorToCarrier n (associatedAmbientEquiv n z) =
      projectiveBase n z :=
  associatedToAmbient_base n z

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

def ambientAssociatedSphereEquiv (n : ℕ) (S : QuaternionicStructure E) :
    ℙ ℂ (V n) ≃ AssociatedSphereFiber n S :=
  (associatedAmbientEquiv n).symm.trans
    (associatedCorrectedHopfEquiv n S)

theorem ambientAssociatedSphereEquiv_base (n : ℕ)
    (S : QuaternionicStructure E) (p : ℙ ℂ (V n)) :
    sphereBase n S (ambientAssociatedSphereEquiv n S p) =
      twistorToCarrier n p := by
  let z := (associatedAmbientEquiv n).symm p
  have hz : associatedAmbientEquiv n z = p :=
    (associatedAmbientEquiv n).apply_symm_apply p
  change sphereBase n S (associatedCorrectedHopfEquiv n S z) =
    twistorToCarrier n p
  rw [associatedCorrectedHopfEquiv_base, ← associatedAmbientEquiv_base n z, hz]

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientEquiv
