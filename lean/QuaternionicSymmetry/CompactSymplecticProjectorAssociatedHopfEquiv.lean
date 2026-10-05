import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedHopf
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfEquiv

/-! The checked Hopf bijection induces a genuine equivalence of associated
total spaces over the projector quotient. It does not, by itself, assert
their identification with ambient CP^{2n+1} or the LC twistor bundle. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedHopfEquiv

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedBase
open CompactSymplecticProjectorAssociatedCorrectedHopf
open CompactSymplecticProjectorStabilizerHopfAction
open FourDimensionalHalfSpinProjective
open FourDimensionalHalfSpinHopfProjectiveDescent
open FourDimensionalHalfSpinHopfEquiv
open FourDimensionalHalfSpinAntipodalVerticalSign
open ManifoldTwistorSphereBundle

noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := firstPairStabilizer n

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

private theorem hopfInverse_equivariant (n : ℕ)
    (S : QuaternionicStructure E) (k : K n) (a : coefficientSphere) :
    letI := projectiveFiberAction n
    letI := sphereFiberAction n S
    projectiveHopfEquiv.symm (k • a) =
      k • projectiveHopfEquiv.symm a := by
  letI := projectiveFiberAction n
  letI := sphereFiberAction n S
  apply projectiveHopfEquiv.injective
  change projectiveHopf (projectiveHopfEquiv.symm (k • a)) =
    projectiveHopf (k • projectiveHopfEquiv.symm a)
  rw [projectiveHopf_stabilizer_equivariant n S k (projectiveHopfEquiv.symm a)]
  change projectiveHopfEquiv (projectiveHopfEquiv.symm (k • a)) =
    k • projectiveHopfEquiv (projectiveHopfEquiv.symm a)
  simp

def associatedHopfInverse (n : ℕ) (S : QuaternionicStructure E) :
    AssociatedSphereFiber n S → AssociatedProjectiveFiber n := by
  letI := projectiveFiberAction n
  letI := sphereFiberAction n S
  refine Quotient.lift (fun z : G n × coefficientSphere =>
    (⟦(z.1, projectiveHopfEquiv.symm z.2)⟧ : AssociatedProjectiveFiber n)) ?_
  intro a b hab
  change ∃ k : K n, (associatedAction n).smul k b = a at hab
  rcases hab with ⟨k, hk⟩
  apply Quotient.sound
  change ∃ k : K n, (associatedAction n).smul k
    (b.1, projectiveHopfEquiv.symm b.2) =
      (a.1, projectiveHopfEquiv.symm a.2)
  refine ⟨k, ?_⟩
  rw [← hk]
  apply Prod.ext
  · rfl
  · exact (hopfInverse_equivariant n S k b.2).symm

def associatedHopfEquiv (n : ℕ) (S : QuaternionicStructure E) :
    AssociatedProjectiveFiber n ≃ AssociatedSphereFiber n S where
  toFun := associatedHopf n S
  invFun := associatedHopfInverse n S
  left_inv z := by
    induction z using Quotient.inductionOn with
    | _ z =>
      change (⟦(z.1, projectiveHopfEquiv.symm (projectiveHopf z.2))⟧ :
        AssociatedProjectiveFiber n) = ⟦z⟧
      have h : projectiveHopfEquiv.symm (projectiveHopf z.2) = z.2 :=
        projectiveHopfEquiv.symm_apply_apply z.2
      rw [h]
  right_inv z := by
    induction z using Quotient.inductionOn with
    | _ z =>
      change (⟦(z.1, projectiveHopf (projectiveHopfEquiv.symm z.2))⟧ :
        AssociatedSphereFiber n S) = ⟦z⟧
      have h : projectiveHopf (projectiveHopfEquiv.symm z.2) = z.2 :=
        projectiveHopfEquiv.apply_symm_apply z.2
      rw [h]

theorem associatedHopfEquiv_base (n : ℕ) (S : QuaternionicStructure E)
    (z : AssociatedProjectiveFiber n) :
    sphereBase n S (associatedHopfEquiv n S z) = projectiveBase n z :=
  associatedHopf_base n S z

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedHopfEquiv
