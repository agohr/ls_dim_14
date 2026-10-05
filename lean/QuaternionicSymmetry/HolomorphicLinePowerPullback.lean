import QuaternionicSymmetry.HolomorphicLineCorePullback
import QuaternionicSymmetry.HolomorphicLineTensorPowerClasses

/-! Compatibility of the actual scalar-cocycle tensor powers with
holomorphic restriction to a complex submanifold. -/

namespace QuaternionicSymmetry.HolomorphicLinePowerPullback

open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLinePowers
open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section
universe u

variable {B B' H H' F F' ι : Type*}
  [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace H]
  [TopologicalSpace H'] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [ChartedSpace H B] [ChartedSpace H' B']
  (IB : ModelWithCorners ℂ F H) (IB' : ModelWithCorners ℂ F' H')
  (Z : VectorBundleCore ℂ B ℂ ι)
  (f : B' → B) (hf : ContMDiff IB' IB ∞ f) (k : ℕ)

theorem pullbackCore_powerCore :
    pullbackCore (powerCore Z k) f hf.continuous =
      powerCore (pullbackCore Z f hf.continuous) k := by
  rfl

theorem pullbackLineCore_powerCore (L : LineCore.{u} (B := B) IB) :
    pullbackLineCore IB IB' (powerCoreRep IB L k) f hf =
      powerCoreRep IB' (pullbackLineCore IB IB' L f hf) k := by
  cases L
  rfl

end
end QuaternionicSymmetry.HolomorphicLinePowerPullback
