import QuaternionicSymmetry.HolomorphicLineDerivedTensor
import QuaternionicSymmetry.HolomorphicExponentialCohomology
import QuaternionicSymmetry.SimplyConnectedIntegralCohomology
import QuaternionicSymmetry.FiniteRankOneAbelian

/-! The Picard-group algebra applied to genuine holomorphic line classes
and actual integral derived H². Vanishing, simple connectedness, finite
generation, rank and the degree map are all explicit. In particular, none
of the still-open geometric T2 inputs is packaged as a literature source. -/

namespace QuaternionicSymmetry.HolomorphicLineCyclicCohomology

open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicExponentialCohomology SimplyConnectedIntegralCohomology
open FiniteRankOneAbelian
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

def lineClassIntegralEquiv
    (hvan₁ : Subsingleton (functionCohomology (B := B) IB 1))
    (hvan₂ : Subsingleton (functionCohomology (B := B) IB 2)) :
    Additive (CoreClass.{0} (B := B) IB) ≃+
      integralCohomology (B := B) 2 :=
  (HolomorphicLineDerivedTensor.classAddEquiv IB).trans
    (exponentialCohomologyEquiv IB 1 hvan₁ hvan₂)

variable [SimplyConnectedSpace B] [LocPathConnectedSpace B] [Nonempty B]

theorem lineClass_isAddTorsionFree
    (hvan₁ : Subsingleton (functionCohomology (B := B) IB 1))
    (hvan₂ : Subsingleton (functionCohomology (B := B) IB 2)) :
    IsAddTorsionFree (Additive (CoreClass.{0} (B := B) IB)) := by
  letI := integralCohomology_two_torsionFree B
  exact (lineClassIntegralEquiv IB hvan₁ hvan₂).injective.isAddTorsionFree
    (lineClassIntegralEquiv IB hvan₁ hvan₂).toAddMonoidHom

def lineClassIntegerEquiv
    (hvan₁ : Subsingleton (functionCohomology (B := B) IB 1))
    (hvan₂ : Subsingleton (functionCohomology (B := B) IB 2))
    (hFinite : Module.Finite ℤ (integralCohomology (B := B) 2))
    (hRank : Module.finrank ℤ (integralCohomology (B := B) 2) = 1) :
    Additive (CoreClass.{0} (B := B) IB) ≃+ ℤ := by
  letI := integralCohomology_two_torsionFree B
  letI := hFinite
  exact (lineClassIntegralEquiv IB hvan₁ hvan₂).trans
    (integerEquiv (integralCohomology (B := B) 2) hRank)

/-- A genuine integer-valued additive restriction degree of two bounds
the index of a line class by two. No restriction-degree theorem is assumed
implicitly; its construction is a separate geometric obligation. -/
theorem exists_lineClass_coordinate_one_or_two
    (hvan₁ : Subsingleton (functionCohomology (B := B) IB 1))
    (hvan₂ : Subsingleton (functionCohomology (B := B) IB 2))
    (hFinite : Module.Finite ℤ (integralCohomology (B := B) 2))
    (hRank : Module.finrank ℤ (integralCohomology (B := B) 2) = 1)
    (degree : Additive (CoreClass.{0} (B := B) IB) →+ ℤ)
    (L : CoreClass.{0} (B := B) IB)
    (hDegree : degree (Additive.ofMul L) = 2) :
    ∃ e : Additive (CoreClass.{0} (B := B) IB) ≃+ ℤ,
      e (Additive.ofMul L) = 1 ∨ e (Additive.ofMul L) = 2 :=
  exists_coordinate_one_or_two
    (lineClassIntegerEquiv IB hvan₁ hvan₂ hFinite hRank)
    degree (Additive.ofMul L) hDegree

end
end QuaternionicSymmetry.HolomorphicLineCyclicCohomology
