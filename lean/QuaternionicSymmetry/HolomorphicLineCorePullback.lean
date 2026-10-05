import QuaternionicSymmetry.HolomorphicLineCoreClasses
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-! Pullback of actual holomorphic line cores along holomorphic maps. This
provides the genuine restricted line core when the map is the inclusion of
a complex submanifold; no section-dimension estimate is assumed here. -/

namespace QuaternionicSymmetry.HolomorphicLineCorePullback

open scoped Manifold ContDiff
noncomputable section
universe u

variable {B B' H H' F F' : Type*}
  [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace H]
  [TopologicalSpace H'] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [ChartedSpace H B] [ChartedSpace H' B']
  (IB : ModelWithCorners ℂ F H)
  (IB' : ModelWithCorners ℂ F' H')

/-- Pull back a line core by a continuous base map, retaining its actual
transition functions on the inverse-image cover. -/
def pullbackCore {ι : Type*} (Z : VectorBundleCore ℂ B ℂ ι)
    (f : B' → B) (hf : Continuous f) : VectorBundleCore ℂ B' ℂ ι where
  baseSet i := f ⁻¹' Z.baseSet i
  isOpen_baseSet i := (Z.isOpen_baseSet i).preimage hf
  indexAt x := Z.indexAt (f x)
  mem_baseSet_at x := Z.mem_baseSet_at (f x)
  coordChange i j x := Z.coordChange i j (f x)
  coordChange_self i x hx v := Z.coordChange_self i (f x) hx v
  continuousOn_coordChange i j := by
    exact (Z.continuousOn_coordChange i j).comp hf.continuousOn
      (by intro x hx; exact hx)
  coordChange_comp i j k x hx v := Z.coordChange_comp i j k (f x) hx v

/-- Holomorphicity of all pullback transition maps follows by composition
with the actual holomorphic base map. -/
instance pullbackCore_isContMDiff {ι : Type*}
    (Z : VectorBundleCore ℂ B ℂ ι) [Z.IsContMDiff IB ∞]
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f) :
    (pullbackCore Z f hf.continuous).IsContMDiff IB' ∞ where
  contMDiffOn_coordChange i j := by
    exact (Z.contMDiffOn_coordChange IB i j).comp hf.contMDiffOn
      (by intro x hx; exact hx)

/-- A genuinely holomorphic line core on the source manifold of `f`.
Taking `f` to be a complex-submanifold inclusion gives the restricted line. -/
def pullbackLineCore
    (L : HolomorphicLineCoreClasses.LineCore.{u} (B := B) IB)
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f) :
    HolomorphicLineCoreClasses.LineCore.{u} (B := B') IB' := by
  letI := L.holomorphic
  exact {
    Index := L.Index
    core := pullbackCore L.core f hf.continuous
    holomorphic := pullbackCore_isContMDiff IB IB' L.core f hf }

/-- The genuine global holomorphic sections of any represented line core,
including a line obtained by restriction to a complex submanifold. -/
abbrev GlobalSections
    (L : HolomorphicLineCoreClasses.LineCore.{u} (B := B) IB) : Type _ := by
  letI := L.holomorphic
  exact ContMDiffSection IB ℂ ∞ L.core.Fiber

/-- The actual restricted holomorphic section space for a holomorphic
inclusion `f : B' → B`; it is not identified with restrictions of ambient
sections, since extension need not hold. -/
abbrev RestrictedGlobalSections
    (L : HolomorphicLineCoreClasses.LineCore.{u} (B := B) IB)
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f) : Type _ :=
  GlobalSections IB' (pullbackLineCore IB IB' L f hf)

end
end QuaternionicSymmetry.HolomorphicLineCorePullback
