import QuaternionicSymmetry.HolomorphicLineCoreClassPowers
import QuaternionicSymmetry.HolomorphicLineHermitianGaugeCurvature
import QuaternionicSymmetry.HolomorphicLineHermitianPositiveRoot
import QuaternionicSymmetry.FiniteRankOneAbelian

/-! A positive line class with positive integer coordinate has an actual
positive primitive holomorphic root. The root is a genuine line core,
its power comparison is a holomorphic gauge, and its positivity is obtained
by pulling back the supplied metric and taking the proved positive root.
No Picard-rank or projective-space characterization is assumed implicitly. -/

namespace QuaternionicSymmetry.HolomorphicLinePositivePrimitiveRoot

open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicLineCoreClassPowers HolomorphicLineTensorPowerClasses
open HolomorphicLineHermitianMetric HolomorphicLineHermitianPositiveRoot
open HolomorphicLineHermitianGauge HolomorphicLineHermitianGaugeCurvature
open FiniteRankOneAbelian
open scoped Manifold ContDiff
noncomputable section

universe uB uF uI
variable {B : Type uB} {F : Type uF}
  [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F B]

theorem exists_positive_primitive_root
    (L : LineCore.{uI} (B := B) 𝓘(ℂ,F))
    (e : Additive (CoreClass.{uI} (B := B) 𝓘(ℂ,F)) ≃+ ℤ)
    (k : ℕ) (hk : 0 < k)
    (hL : e (Additive.ofMul (Quotient.mk _ L)) = (k : ℤ))
    (m : HermitianLineMetric L) (hm : m.PositiveChernCurvature L) :
    ∃ H : LineCore.{uI} (B := B) 𝓘(ℂ,F),
      e (Additive.ofMul (Quotient.mk _ H)) = 1 ∧
      Function.Bijective (fun r : ℤ =>
        (Quotient.mk _ H : CoreClass 𝓘(ℂ,F)) ^ r) ∧
      Isomorphic 𝓘(ℂ,F) (powerCoreRep 𝓘(ℂ,F) H k) L ∧
      ∃ mH : HermitianLineMetric H, mH.PositiveChernCurvature H := by
  let a : CoreClass.{uI} (B := B) 𝓘(ℂ,F) := (e.symm 1).toMul
  obtain ⟨H, hH⟩ := Quotient.exists_rep a
  have heH : e (Additive.ofMul (Quotient.mk _ H)) = 1 := by
    rw [hH]
    exact e.apply_symm_apply 1
  have hbij : Function.Bijective (fun r : ℤ =>
      (Quotient.mk _ H : CoreClass 𝓘(ℂ,F)) ^ r) :=
    zsmul_bijective_of_coordinate_one e (Additive.ofMul (Quotient.mk _ H)) heH
  have hclass : (Quotient.mk _ (powerCoreRep 𝓘(ℂ,F) H k) : CoreClass 𝓘(ℂ,F)) =
      Quotient.mk _ L := by
    apply (show Function.Injective
      (fun c : CoreClass.{uI} (B := B) 𝓘(ℂ,F) => e (Additive.ofMul c)) from
        e.injective)
    change e (Additive.ofMul (Quotient.mk _ (powerCoreRep 𝓘(ℂ,F) H k))) =
      e (Additive.ofMul (Quotient.mk _ L))
    rw [class_powerCoreRep, ofMul_pow, map_nsmul, heH, hL]
    simp
  have hIso : Isomorphic 𝓘(ℂ,F) (powerCoreRep 𝓘(ℂ,F) H k) L :=
    Quotient.exact hclass
  let p := gaugePullbackMetric (powerCoreRep 𝓘(ℂ,F) H k) L hIso m
  have hp : p.PositiveChernCurvature (powerCoreRep 𝓘(ℂ,F) H k) :=
    gaugePullbackMetric_positive _ _ hIso m hm
  exact ⟨H, heH, hbij, hIso, rootMetric H k hk p,
    rootMetric_positive H k hk p hp⟩

end
end QuaternionicSymmetry.HolomorphicLinePositivePrimitiveRoot
