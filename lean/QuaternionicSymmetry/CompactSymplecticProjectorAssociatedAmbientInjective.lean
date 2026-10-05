import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientSurjection

/-! The concrete moved-line map has no identifications beyond the checked
first-pair stabilizer relation: the associated CP¹ total space is bijective
to ambient CP^{2n+1} over the genuine projector quotient. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientInjective

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedBase
open CompactSymplecticProjectorAssociatedToAmbient
open CompactSymplecticProjectorTwistorCarrierMap
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorTwistorAssociatedDescentLinear
open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticProjectorStabilizerHopfAction

noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := firstPairStabilizer n

theorem associatedToAmbient_injective (n : ℕ) :
    Function.Injective (associatedToAmbient n) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      have hbase : (a.1 : ProjectiveCarrier n) = (b.1 : ProjectiveCarrier n) := by
        have h := congrArg (twistorToCarrier n) hab
        rw [associatedToAmbient_base, associatedToAmbient_base] at h
        exact h
      have hmem : a.1⁻¹ * b.1 ∈ K n := QuotientGroup.eq.mp hbase
      let k : K n := ⟨a.1⁻¹ * b.1, hmem⟩
      have hgroup : b.1 * (k⁻¹ : G n) = a.1 := by
        simp [k, mul_assoc]
      letI := projectiveFiberAction n
      have hfiber : a.2 = k • b.2 := by
        apply (fiberProjectiveLine_injective n (firstColumnSphere n a.1))
        calc
          fiberProjectiveLine n (firstColumnSphere n a.1) a.2 =
              fiberProjectiveLine n (firstColumnSphere n b.1) b.2 := hab
          _ = fiberProjectiveLine n
                (firstColumnSphere n (b.1 * (k⁻¹ : G n))) (k • b.2) :=
                  (movedFiber_stabilizer_independent n b.1 k b.2).symm
          _ = fiberProjectiveLine n (firstColumnSphere n a.1) (k • b.2) := by
                rw [hgroup]
      apply Quotient.sound
      change ∃ l : K n, (associatedAction n).smul l b = a
      refine ⟨k, ?_⟩
      exact Prod.ext hgroup hfiber.symm

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientInjective
