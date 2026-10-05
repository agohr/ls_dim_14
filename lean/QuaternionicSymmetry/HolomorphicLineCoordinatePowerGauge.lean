import QuaternionicSymmetry.HolomorphicLineCoreClassPowers

/-! Integer line-class coordinates determine genuine holomorphic power
gauges. The class equivalence is explicit; no Picard computation is hidden
in this algebraic-to-geometric transport. -/

namespace QuaternionicSymmetry.HolomorphicLineCoordinatePowerGauge

open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicLineCoreClassPowers HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section

universe uB uF uI
variable {B : Type uB} {F : Type uF}
  [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F B]

theorem isomorphic_power_of_coordinate
    (H L : LineCore.{uI} (B := B) 𝓘(ℂ,F))
    (e : Additive (CoreClass.{uI} (B := B) 𝓘(ℂ,F)) ≃+ ℤ)
    (hH : e (Additive.ofMul (Quotient.mk _ H)) = 1)
    (k : ℕ) (hL : e (Additive.ofMul (Quotient.mk _ L)) = (k : ℤ)) :
    Isomorphic 𝓘(ℂ,F) (powerCoreRep 𝓘(ℂ,F) H k) L := by
  suffices hclass :
      (Quotient.mk _ (powerCoreRep 𝓘(ℂ,F) H k) : CoreClass.{uI} 𝓘(ℂ,F)) =
        Quotient.mk _ L by
    exact Quotient.exact hclass
  apply (show Function.Injective
    (fun c : CoreClass.{uI} (B := B) 𝓘(ℂ,F) => e (Additive.ofMul c)) from
      e.injective)
  change e (Additive.ofMul (Quotient.mk _ (powerCoreRep 𝓘(ℂ,F) H k))) =
    e (Additive.ofMul (Quotient.mk _ L))
  rw [class_powerCoreRep, ofMul_pow, map_nsmul, hH, hL]
  simp

end
end QuaternionicSymmetry.HolomorphicLineCoordinatePowerGauge
