import QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
import QuaternionicSymmetry.HolomorphicLineCorePullbackSections

/-! Pointwise powers of genuine holomorphic sections of represented line cores. -/

namespace QuaternionicSymmetry.HolomorphicLinePowerSections

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H) [IsManifold IB ∞ B]
  (L : LineCore.{u} (B := B) IB)

/-- The pointwise `k`-th power is a section of the actual scalar-cocycle
tensor power, not a section of the original line. -/
def powerSection (s : GlobalSections IB L) (k : ℕ) :
    GlobalSections IB (powerCoreRep IB L k) := by
  letI := L.holomorphic
  let P := powerCoreRep IB L k
  letI := P.holomorphic
  letI : ContMDiffVectorBundle ∞ ℂ P.core.Fiber IB :=
    VectorBundleCore.instContMDiffVectorBundle P.core
  refine ⟨fun x => ((show ℂ from s x) ^ k : ℂ), ?_⟩
  intro y
  let e := trivializationAt ℂ L.core.Fiber y
  let e' := trivializationAt ℂ P.core.Fiber y
  have hy : y ∈ e.baseSet := L.core.mem_baseSet_at y
  have hy' : y ∈ e'.baseSet := P.core.mem_baseSet_at y
  apply (e'.contMDiffAt_section_iff hy').2
  have hs : ContMDiffAt IB 𝓘(ℂ, ℂ) ∞
      (fun x => (e ⟨x, s x⟩).2) y :=
    (e.contMDiffAt_section_iff hy).1 (s.contMDiff y)
  apply (hs.pow k).congr_of_eventuallyEq
  filter_upwards [L.core.isOpen_baseSet (L.core.indexAt y) |>.mem_nhds hy] with x hx
  change (P.core.coordChange (P.core.indexAt x) (P.core.indexAt y) x)
      ((show ℂ from s x) ^ k) =
    ((L.core.coordChange (L.core.indexAt x) (L.core.indexAt y) x) (s x)) ^ k
  simp only [P, powerCoreRep, HolomorphicLinePowers.powerCore,
    HolomorphicLinePowers.transitionScalar, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [HolomorphicLinePowers.linear_apply_one
    (L.core.coordChange (L.core.indexAt x) (L.core.indexAt y) x) (s x)]
  simp only [mul_pow]

end
end QuaternionicSymmetry.HolomorphicLinePowerSections
