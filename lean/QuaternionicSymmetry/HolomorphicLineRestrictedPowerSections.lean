import QuaternionicSymmetry.HolomorphicLinePowerPullback
import QuaternionicSymmetry.HolomorphicLineCorePullbackSections

/-! Sections of an ambient tensor power restrict to actual holomorphic
sections of the matching power of the pulled-back line. -/

namespace QuaternionicSymmetry.HolomorphicLineRestrictedPowerSections
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section

variable {B B' H H' F F' : Type*}
  [TopologicalSpace B] [TopologicalSpace B']
  [TopologicalSpace H] [TopologicalSpace H']
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [ChartedSpace H B] [ChartedSpace H' B']
  (IB : ModelWithCorners ℂ F H) (IB' : ModelWithCorners ℂ F' H')
  (L : LineCore.{0} (B := B) IB)
  (f : B' → B) (hf : ContMDiff IB' IB ∞ f) (k : ℕ)

def restrictedPowerSection
    (t : GlobalSections IB (powerCoreRep IB L k)) :
    GlobalSections IB' (powerCoreRep IB'
      (pullbackLineCore IB IB' L f hf) k) := by
  change GlobalSections IB'
    (pullbackLineCore IB IB' (powerCoreRep IB L k) f hf)
  exact restrictionLinear IB IB' (powerCoreRep IB L k) f hf t

theorem restrictedPowerSection_apply
    (t : GlobalSections IB (powerCoreRep IB L k)) (x : B') :
    restrictedPowerSection IB IB' L f hf k t x = t (f x) := rfl

end
end QuaternionicSymmetry.HolomorphicLineRestrictedPowerSections
