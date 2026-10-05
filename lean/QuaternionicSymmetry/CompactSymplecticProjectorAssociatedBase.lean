import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedHopf

/-! Both genuine associated fibers lie over the actual Sp(n+1)/K projector
quotient. The descended Hopf map preserves that base point. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedBase

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorStabilizerHopfAction
open FourDimensionalHalfSpinProjective
open FourDimensionalTwistorNormalizerQuotient
open ManifoldTwistorSphereBundle

noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := firstPairStabilizer n

private theorem coset_associated_smul (n : ℕ) (u : G n) (k : K n) :
    ((u * (k⁻¹ : G n) : G n) : ProjectiveCarrier n) =
      (u : ProjectiveCarrier n) := by
  exact QuotientGroup.mk_mul_of_mem u (show (k⁻¹ : G n) ∈ K n from k⁻¹.property)

def projectiveBase (n : ℕ) : AssociatedProjectiveFiber n → ProjectiveCarrier n := by
  letI := projectiveFiberAction n
  refine Quotient.lift (fun z : G n × ProjectiveSpinor =>
    (z.1 : ProjectiveCarrier n)) ?_
  intro a b hab
  change ∃ k : K n, (associatedAction n).smul k b = a at hab
  rcases hab with ⟨k, hk⟩
  rw [← hk]
  exact coset_associated_smul n b.1 k

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

def sphereBase (n : ℕ) (S : QuaternionicStructure E) :
    AssociatedSphereFiber n S → ProjectiveCarrier n := by
  letI := sphereFiberAction n S
  refine Quotient.lift (fun z : G n × coefficientSphere =>
    (z.1 : ProjectiveCarrier n)) ?_
  intro a b hab
  change ∃ k : K n, (associatedAction n).smul k b = a at hab
  rcases hab with ⟨k, hk⟩
  rw [← hk]
  exact coset_associated_smul n b.1 k

@[simp] theorem projectiveBase_mk (n : ℕ) (u : G n) (p : ProjectiveSpinor) :
    projectiveBase n (⟦(u, p)⟧ : AssociatedProjectiveFiber n) =
      (u : ProjectiveCarrier n) := rfl

@[simp] theorem sphereBase_mk (n : ℕ) (S : QuaternionicStructure E)
    (u : G n) (a : coefficientSphere) :
    sphereBase n S (⟦(u, a)⟧ : AssociatedSphereFiber n S) =
      (u : ProjectiveCarrier n) := rfl

/-- The associated Hopf map is a map of bundles over the actual quotient. -/
theorem associatedHopf_base (n : ℕ) (S : QuaternionicStructure E)
    (z : AssociatedProjectiveFiber n) :
    sphereBase n S (associatedHopf n S z) = projectiveBase n z := by
  induction z using Quotient.inductionOn with
  | _ z => rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedBase
