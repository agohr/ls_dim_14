import QuaternionicSymmetry.CompactSymplecticProjectorStabilizerHopfAction

/-! The checked Hopf map descends through the *actual* first-pair stabilizer
relation on a pair consisting of an Sp(n+1) representative and a fiber point.
No choice of a representative enters the resulting associated-bundle map. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedHopf

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStabilizerHopfAction
open FourDimensionalHalfSpinProjective
open FourDimensionalHalfSpinHopfProjectiveDescent
open FourDimensionalTwistorNormalizerQuotient
open ManifoldTwistorSphereBundle

noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := firstPairStabilizer n

/-- The diagonal stabilizer action defining an associated fiber bundle.
The inverse in the group coordinate makes the left action law exact. -/
def associatedAction (n : ℕ) {F : Type*} [MulAction (K n) F] :
    MulAction (K n) (G n × F) where
  smul k z := (z.1 * (k⁻¹ : G n), k • z.2)
  one_smul z := by
    change (z.1 * (((1 : K n)⁻¹ : G n)), (1 : K n) • z.2) = z
    simp
  mul_smul k l z := by
    change (z.1 * (((k * l)⁻¹ : G n)), (k * l) • z.2) =
      ((z.1 * (l⁻¹ : G n)) * (k⁻¹ : G n), k • (l • z.2))
    simp [mul_assoc, mul_smul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

abbrev AssociatedProjectiveFiber (n : ℕ) :=
  letI := projectiveFiberAction n
  Quotient (@MulAction.orbitRel (K n) (G n × ProjectiveSpinor) _
    (associatedAction n))

abbrev AssociatedSphereFiber (n : ℕ) (S : QuaternionicStructure E) :=
  letI := sphereFiberAction n S
  Quotient (@MulAction.orbitRel (K n) (G n × coefficientSphere) _
    (associatedAction n))

/-- The genuine stabilizer-equivariant Hopf map on representatives. -/
theorem associatedHopf_equivariant (n : ℕ) (S : QuaternionicStructure E)
    (k : K n) (z : G n × ProjectiveSpinor) :
    letI := projectiveFiberAction n
    letI := sphereFiberAction n S
    (fun z : G n × ProjectiveSpinor => (z.1, projectiveHopf z.2))
      ((associatedAction n).smul k z) =
      (associatedAction n).smul k (z.1, projectiveHopf z.2) := by
  letI := projectiveFiberAction n
  letI := sphereFiberAction n S
  apply Prod.ext
  · rfl
  · exact projectiveHopf_stabilizer_equivariant n S k z.2

/-- A stabilizer-independent Hopf map between the actual associated fibers. -/
def associatedHopf (n : ℕ) (S : QuaternionicStructure E) :
    AssociatedProjectiveFiber n → AssociatedSphereFiber n S := by
  letI := projectiveFiberAction n
  letI := sphereFiberAction n S
  refine Quotient.lift (fun z : G n × ProjectiveSpinor =>
    (⟦(z.1, projectiveHopf z.2)⟧ : AssociatedSphereFiber n S)) ?_
  intro a b hab
  change ∃ k : K n, (associatedAction n).smul k b = a at hab
  rcases hab with ⟨k, hk⟩
  apply Quotient.sound
  change ∃ k : K n, (associatedAction n).smul k
    (b.1, projectiveHopf b.2) = (a.1, projectiveHopf a.2)
  refine ⟨k, ?_⟩
  rw [← hk]
  exact (associatedHopf_equivariant n S k b).symm

@[simp] theorem associatedHopf_mk (n : ℕ) (S : QuaternionicStructure E)
    (u : G n) (p : ProjectiveSpinor) :
    associatedHopf n S (⟦(u, p)⟧ : AssociatedProjectiveFiber n) =
      (⟦(u, projectiveHopf p)⟧ : AssociatedSphereFiber n S) := by
  simp only [associatedHopf, Quotient.lift_mk]

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedHopf
