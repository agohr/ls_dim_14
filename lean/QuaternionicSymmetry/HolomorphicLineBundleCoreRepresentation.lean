import QuaternionicSymmetry.HolomorphicLineCoreClasses
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! Every genuine holomorphic vector bundle with model fiber ℂ has a
holomorphic line core indexed by its base points. Its cocycle consists of
the actual bundle's preferred-trivialization coordinate changes. This is
the representation construction, not yet its total-bundle isomorphism or
the comparison with all invertible analytic sheaves. -/

namespace QuaternionicSymmetry.HolomorphicLineBundleCoreRepresentation

open HolomorphicLineCoreClasses Bundle
open scoped Manifold ContDiff
noncomputable section

universe u v
variable {B : Type u} {H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (V : B → Type v) [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
  [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

/-- A core extracted from an arbitrary actual holomorphic line bundle,
using one genuine trivialization around each point. -/
def bundleCore : VectorBundleCore ℂ B ℂ B where
  baseSet i := (trivializationAt ℂ V i).baseSet
  isOpen_baseSet i := (trivializationAt ℂ V i).open_baseSet
  indexAt x := x
  mem_baseSet_at x := FiberBundle.mem_baseSet_trivializationAt ℂ V x
  coordChange i j x :=
    ((trivializationAt ℂ V i).coordChangeL ℂ (trivializationAt ℂ V j) x).toContinuousLinearMap
  coordChange_self i x hx z := by
    change (trivializationAt ℂ V i).coordChangeL ℂ (trivializationAt ℂ V i) x z = z
    rw [Trivialization.coe_coordChangeL _ _ ⟨hx, hx⟩]
    exact (trivializationAt ℂ V i).linearEquivAt ℂ x hx |>.apply_symm_apply z
  continuousOn_coordChange i j :=
    continuousOn_coordChange ℂ (trivializationAt ℂ V i) (trivializationAt ℂ V j)
  coordChange_comp i j k x hx z := by
    change (trivializationAt ℂ V j).coordChangeL ℂ (trivializationAt ℂ V k) x
        ((trivializationAt ℂ V i).coordChangeL ℂ (trivializationAt ℂ V j) x z) =
      (trivializationAt ℂ V i).coordChangeL ℂ (trivializationAt ℂ V k) x z
    rw [Trivialization.coe_coordChangeL _ _ ⟨hx.1.2, hx.2⟩,
      Trivialization.coe_coordChangeL _ _ hx.1,
      Trivialization.coe_coordChangeL _ _ ⟨hx.1.1, hx.2⟩]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

instance bundleCore_holomorphic [ContMDiffVectorBundle ∞ ℂ V IB] :
    (bundleCore V).IsContMDiff IB ∞ where
  contMDiffOn_coordChange i j :=
    contMDiffOn_coordChangeL (trivializationAt ℂ V i) (trivializationAt ℂ V j)

/-- The represented holomorphic line associated to any genuine bundle
with holomorphic one-dimensional complex local trivializations. -/
def representedLine [ContMDiffVectorBundle ∞ ℂ V IB] : LineCore.{u} (B := B) IB where
  Index := B
  core := bundleCore V
  holomorphic := inferInstance

/-- Pointwise linear comparison with the original fiber; regularity of
the resulting total map requires the subsequent fixed-chart argument. -/
def representationFiberEquiv (x : B) : (bundleCore V).Fiber x ≃ₗ[ℂ] V x :=
  ((trivializationAt ℂ V x).linearEquivAt ℂ x
    (FiberBundle.mem_baseSet_trivializationAt ℂ V x)).symm

theorem representationFiberEquiv_coordinates
    (i x : B) (z : (bundleCore V).Fiber x)
    (hx : x ∈ (trivializationAt ℂ V i).baseSet) :
    ((trivializationAt ℂ V i) ⟨x, representationFiberEquiv V x z⟩).2 =
      (((bundleCore V).localTriv i) ⟨x, z⟩).2 := by
  change ((trivializationAt ℂ V i).linearEquivAt ℂ x hx)
      (representationFiberEquiv V x z) =
    (trivializationAt ℂ V x).coordChangeL ℂ (trivializationAt ℂ V i) x z
  rw [Trivialization.coe_coordChangeL _ _
    ⟨FiberBundle.mem_baseSet_trivializationAt ℂ V x, hx⟩]
  rfl

end
end QuaternionicSymmetry.HolomorphicLineBundleCoreRepresentation
