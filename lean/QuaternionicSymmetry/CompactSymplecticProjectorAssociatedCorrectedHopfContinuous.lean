import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedHopf
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfContinuous

/-! Continuity of the orientation-corrected Hopf map between the two
concrete Sp-associated quotient bundles. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedHopfContinuous

open Topology
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedCorrectedHopf
open CompactSymplecticProjectorStabilizerHopfAction
open FourDimensionalHalfSpinProjective
open FourDimensionalHalfSpinHopfContinuous
open FourDimensionalHalfSpinHopfProjectiveDescent
open FourDimensionalHalfSpinAntipodalVerticalSign
open ManifoldTwistorSphereBundle

noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := firstPairStabilizer n

theorem continuous_antipodalCoefficient :
    Continuous (antipodalCoefficient : coefficientSphere → coefficientSphere) := by
  have h : Continuous (fun z : coefficientSphere => -(z.1 : Fin 3 → ℝ)) :=
    continuous_neg.comp continuous_subtype_val
  exact h.subtype_mk _

theorem continuous_associatedCorrectedHopf
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    (n : ℕ) (S : QuaternionicStructure E) :
    Continuous (associatedCorrectedHopf n S) := by
  letI := projectiveFiberAction n
  letI := sphereFiberAction n S
  let s := @MulAction.orbitRel (K n) (G n × ProjectiveSpinor) _
    (associatedAction n)
  have hquot : IsQuotientMap (@Quotient.mk' (G n × ProjectiveSpinor) s) :=
    isQuotientMap_quotient_mk'
  apply hquot.continuous_iff.mpr
  have hpair : Continuous (fun z : G n × ProjectiveSpinor =>
      (z.1, antipodalCoefficient (projectiveHopf z.2))) :=
    continuous_fst.prodMk
      (continuous_antipodalCoefficient.comp (projectiveHopf_continuous.comp continuous_snd))
  have hmk : Continuous (@Quotient.mk' (G n × coefficientSphere)
      (@MulAction.orbitRel (K n) (G n × coefficientSphere) _ (associatedAction n))) :=
    continuous_quotient_mk'
  exact (hmk.comp hpair).congr (fun z => by
    exact (associatedCorrectedHopf_mk n S z.1 z.2).symm)

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedHopfContinuous
