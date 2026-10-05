import QuaternionicSymmetry.HolomorphicLineCyclicCohomology
import QuaternionicSymmetry.RankOneDegreeInjection

/-! Strengthened Picard-generator algebra: finite generation need not be
an additional topological premise. A genuine degree-two restriction map
already supplies it once actual integral H² is torsion-free of rank one. -/

namespace QuaternionicSymmetry.HolomorphicLineDegreeGenerator

open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicExponentialCohomology HolomorphicLineCyclicCohomology
open SimplyConnectedIntegralCohomology RankOneDegreeInjection
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  [SimplyConnectedSpace B] [LocPathConnectedSpace B] [Nonempty B]

theorem exists_coordinate_one_or_two_of_degree
    (hvan₁ : Subsingleton (functionCohomology (B := B) IB 1))
    (hvan₂ : Subsingleton (functionCohomology (B := B) IB 2))
    (hRank : Module.finrank ℤ (integralCohomology (B := B) 2) = 1)
    (degree : Additive (CoreClass.{0} (B := B) IB) →+ ℤ)
    (L : CoreClass.{0} (B := B) IB)
    (hDegree : degree (Additive.ofMul L) = 2) :
    ∃ e : Additive (CoreClass.{0} (B := B) IB) ≃+ ℤ,
      e (Additive.ofMul L) = 1 ∨ e (Additive.ofMul L) = 2 := by
  letI := integralCohomology_two_torsionFree B
  let c := lineClassIntegralEquiv IB hvan₁ hvan₂
  let d : integralCohomology (B := B) 2 →+ ℤ :=
    degree.comp c.symm.toAddMonoidHom
  have hd : d (c (Additive.ofMul L)) = 2 := by
    simpa only [d, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddEquiv.symm_apply_apply] using hDegree
  obtain ⟨e, he⟩ := RankOneDegreeInjection.exists_coordinate_one_or_two_of_degree
    hRank d (c (Additive.ofMul L)) hd
  exact ⟨c.trans e, he⟩

end
end QuaternionicSymmetry.HolomorphicLineDegreeGenerator
