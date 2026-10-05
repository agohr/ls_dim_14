import QuaternionicSymmetry.HolomorphicLineGaugeSectionEquiv
import QuaternionicSymmetry.HolomorphicLineCorePullbackLocalSections

/-! A local holomorphic gauge remains a local holomorphic gauge after
restriction along a holomorphic map. -/
namespace QuaternionicSymmetry.HolomorphicLineGaugePullbackSections
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineLocalGaugeRatio
open HolomorphicLineCorePullbackLocalSections
open HolomorphicLineGaugeSectionEquiv
open scoped Manifold ContDiff
noncomputable section

variable {B B' H H' F F' : Type*}
  [TopologicalSpace B] [TopologicalSpace B']
  [TopologicalSpace H] [TopologicalSpace H']
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [ChartedSpace H B] [ChartedSpace H' B']
  (IB : ModelWithCorners ℂ F H) (IB' : ModelWithCorners ℂ F' H')
  (L M : LineCore.{0} (B := B) IB)
  (f : B' → B) (hf : ContMDiff IB' IB ∞ f)
  (e : ∀ x : B, L.core.Fiber x ≃ₗ[ℂ] M.core.Fiber x)

private def pulledEquiv (x : B') :
    (pullbackLineCore IB IB' L f hf).core.Fiber x ≃ₗ[ℂ]
      (pullbackLineCore IB IB' M f hf).core.Fiber x := e (f x)

theorem pullback_hasLocalHolomorphicWitness
    (h : HasLocalHolomorphicWitness IB L.core M.core e) :
    HasLocalHolomorphicWitness IB'
      (pullbackLineCore IB IB' L f hf).core
      (pullbackLineCore IB IB' M f hf).core
      (pulledEquiv IB IB' L M f hf e) := by
  letI := L.holomorphic
  letI := M.holomorphic
  intro x
  obtain ⟨U,hU,hx,s,t,hs,ht,hsx,hmap⟩ := h (f x)
  refine ⟨f ⁻¹' U, hU.preimage hf.continuous, hx,
    (fun y => s (f y)), (fun y => t (f y)), ?_, ?_, hsx, ?_⟩
  · exact alongMap_contMDiffOn_pullback IB IB' L.core f hf
      (f ⁻¹' U) (fun y => s (f y))
      (hs.comp hf.contMDiffOn (by intro y hy; exact hy))
  · exact alongMap_contMDiffOn_pullback IB IB' M.core f hf
      (f ⁻¹' U) (fun y => t (f y))
      (ht.comp hf.contMDiffOn (by intro y hy; exact hy))
  · intro y hy
    exact hmap (f y) hy

/-- The section equivalence induced by the actual pullback of a gauge. -/
def pullbackSectionLinearEquiv
    (h : HasLocalHolomorphicWitness IB L.core M.core e) :
    GlobalSections IB' (pullbackLineCore IB IB' L f hf) ≃ₗ[ℂ]
      GlobalSections IB' (pullbackLineCore IB IB' M f hf) :=
  sectionLinearEquivOfLocalWitness IB'
    (pullbackLineCore IB IB' L f hf)
    (pullbackLineCore IB IB' M f hf)
    (pulledEquiv IB IB' L M f hf e)
    (pullback_hasLocalHolomorphicWitness IB IB' L M f hf e h)

end
end QuaternionicSymmetry.HolomorphicLineGaugePullbackSections
