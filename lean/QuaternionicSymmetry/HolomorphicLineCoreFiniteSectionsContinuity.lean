import QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Pointwise evaluation detects continuity in the genuine finite-dimensional
space of holomorphic sections. The topology is any Hausdorff topological
complex vector-space topology on that same section space; no continuity of
the family is assumed independently of its values. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreFiniteSectionsContinuity

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (L : LineCore.{u} (B := B) IB)

/-- The actual value of a holomorphic section at every base point. -/
def allEvaluations : GlobalSections IB L →ₗ[ℂ] (B → ℂ) where
  toFun s := fun x => s x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem allEvaluations_injective : Function.Injective (allEvaluations IB L) := by
  intro s t h
  apply ContMDiffSection.ext
  intro x
  exact congrFun h x

variable [TopologicalSpace (GlobalSections IB L)]
  [IsTopologicalAddGroup (GlobalSections IB L)]
  [ContinuousSMul ℂ (GlobalSections IB L)] [T2Space (GlobalSections IB L)]
  [FiniteDimensional ℂ (GlobalSections IB L)]

/-- Finite-dimensional holomorphic section space has exactly the topology
induced by its pointwise values. This is not asserted in infinite dimension. -/
theorem allEvaluations_isClosedEmbedding :
    Topology.IsClosedEmbedding (allEvaluations IB L) :=
  LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (allEvaluations_injective IB L))

/-- A parameterized section is continuous precisely when its value at
each fixed point is continuous in the parameter. -/
theorem continuous_iff_evaluation
    {X : Type*} [TopologicalSpace X] (s : X → GlobalSections IB L) :
    Continuous s ↔ ∀ x : B, Continuous (fun a => s a x) := by
  rw [(allEvaluations_isClosedEmbedding IB L).isEmbedding.continuous_iff]
  exact continuous_pi_iff

/-- For a section action, genuine pointwise joint continuity gives joint
continuity with values in the full finite-dimensional section space. -/
theorem continuous_action_of_evaluation
    {G : Type*} [TopologicalSpace G]
    (T : G → GlobalSections IB L →ₗ[ℂ] GlobalSections IB L)
    (hT : ∀ x : B, Continuous
      (fun p : G × GlobalSections IB L => (T p.1 p.2) x)) :
    Continuous (fun p : G × GlobalSections IB L => T p.1 p.2) :=
  (continuous_iff_evaluation IB L _).2 hT

end
end QuaternionicSymmetry.HolomorphicLineCoreFiniteSectionsContinuity
