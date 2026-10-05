import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedBase
import QuaternionicSymmetry.ManifoldTwistorCorrectedHopf

/-! The antipodally corrected associated Hopf map uses the sign convention
for which the checked CP¹-to-twistor-fiber differential is complex linear.
This is a descent theorem, not yet a total-space holomorphicity claim. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedHopf

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedBase
open CompactSymplecticProjectorStabilizerHopfAction
open FourDimensionalHalfSpinProjective
open FourDimensionalHalfSpinHopfProjectiveDescent
open FourDimensionalHalfSpinAntipodalVerticalSign
open FourDimensionalTwistorNormalizerQuotient
open QuaternionicIsometryNormalizer
open ManifoldTwistorSphereBundle

noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := firstPairStabilizer n

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

theorem antipodal_stabilizer_equivariant (n : ℕ)
    (S : QuaternionicStructure E) (k : K n) (a : coefficientSphere) :
    letI := sphereFiberAction n S
    antipodalCoefficient (k • a) = k • antipodalCoefficient a := by
  letI := sphereFiberAction n S
  apply Subtype.ext
  change -(QuaternionicIsometryNormalizer.rotationLinear S
    (QuaternionicUnitScalarIsometries.unitQuaternionNormalizerAction S
      (stabilizerUnitQuaternionHom n k)) a.1) =
    QuaternionicIsometryNormalizer.rotationLinear S
      (QuaternionicUnitScalarIsometries.unitQuaternionNormalizerAction S
        (stabilizerUnitQuaternionHom n k)) (-a.1)
  exact (map_neg _ _).symm

def associatedAntipodal (n : ℕ) (S : QuaternionicStructure E) :
    AssociatedSphereFiber n S → AssociatedSphereFiber n S := by
  letI := sphereFiberAction n S
  refine Quotient.lift (fun z : G n × coefficientSphere =>
    (⟦(z.1, antipodalCoefficient z.2)⟧ : AssociatedSphereFiber n S)) ?_
  intro a b hab
  change ∃ k : K n, (associatedAction n).smul k b = a at hab
  rcases hab with ⟨k, hk⟩
  apply Quotient.sound
  change ∃ k : K n, (associatedAction n).smul k
    (b.1, antipodalCoefficient b.2) =
      (a.1, antipodalCoefficient a.2)
  refine ⟨k, ?_⟩
  rw [← hk]
  apply Prod.ext
  · rfl
  · exact (antipodal_stabilizer_equivariant n S k b.2).symm

def associatedCorrectedHopf (n : ℕ) (S : QuaternionicStructure E) :
    AssociatedProjectiveFiber n → AssociatedSphereFiber n S :=
  associatedAntipodal n S ∘ associatedHopf n S

@[simp] theorem associatedCorrectedHopf_mk (n : ℕ)
    (S : QuaternionicStructure E) (u : G n) (p : ProjectiveSpinor) :
    associatedCorrectedHopf n S
      (⟦(u, p)⟧ : AssociatedProjectiveFiber n) =
      (⟦(u, antipodalCoefficient (projectiveHopf p))⟧ :
        AssociatedSphereFiber n S) := by
  simp [associatedCorrectedHopf, associatedAntipodal]

theorem associatedCorrectedHopf_base (n : ℕ)
    (S : QuaternionicStructure E) (z : AssociatedProjectiveFiber n) :
    sphereBase n S (associatedCorrectedHopf n S z) =
      projectiveBase n z := by
  induction z using Quotient.inductionOn with
  | _ z => rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedHopf
