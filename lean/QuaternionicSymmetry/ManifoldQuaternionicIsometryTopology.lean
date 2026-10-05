import QuaternionicSymmetry.ManifoldQuaternionicSpanSymmetry
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction

/-! The genuine quaternionic isometry group, topologized by its forward and
inverse maps with the compact-open topology. This constructs the topological
group and its continuous evaluation action, but does not assert compactness,
existence of a Lie structure, or a maximal torus. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryTopology

open ManifoldQuaternionicSpanSymmetry Topology
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def mapPair (f : QuaternionicIsometries Q) : C(M,M) × C(M,M) :=
  (⟨f.1, f.1.continuous⟩, ⟨f.1.symm, f.1.symm.continuous⟩)

instance : TopologicalSpace (QuaternionicIsometries Q) :=
  TopologicalSpace.induced (mapPair Q) inferInstance

theorem mapPair_injective : Function.Injective (mapPair Q) := by
  intro f g h
  apply Subtype.ext
  apply Diffeomorph.ext
  intro x
  exact congrArg (fun p : C(M,M) × C(M,M) => p.1 x) h

theorem mapPair_isEmbedding : IsEmbedding (mapPair Q) :=
  ⟨⟨rfl⟩, mapPair_injective Q⟩

theorem continuous_mapPair : Continuous (mapPair Q) :=
  (mapPair_isEmbedding Q).continuous

instance [T2Space M] : T2Space (QuaternionicIsometries Q) :=
  (mapPair_isEmbedding Q).t2Space

theorem mapPair_inv (f : QuaternionicIsometries Q) :
    mapPair Q f⁻¹ = (mapPair Q f).swap := by
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro x <;> rfl

theorem mapPair_mul (f g : QuaternionicIsometries Q) :
    mapPair Q (f*g) =
      ((mapPair Q f).1.comp (mapPair Q g).1,
       (mapPair Q g).2.comp (mapPair Q f).2) := by
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro x <;> rfl

instance : ContinuousInv (QuaternionicIsometries Q) where
  continuous_inv := by
    apply (mapPair_isEmbedding Q).isInducing.continuous_iff.mpr
    simpa only [Function.comp_def, mapPair_inv] using
      continuous_swap.comp (continuous_mapPair Q)

instance [LocallyCompactSpace M] : ContinuousMul (QuaternionicIsometries Q) where
  continuous_mul := by
    apply (mapPair_isEmbedding Q).isInducing.continuous_iff.mpr
    have hf := (continuous_mapPair Q).comp
      (continuous_fst : Continuous (Prod.fst : QuaternionicIsometries Q ×
        QuaternionicIsometries Q → QuaternionicIsometries Q))
    have hg := (continuous_mapPair Q).comp
      (continuous_snd : Continuous (Prod.snd : QuaternionicIsometries Q ×
        QuaternionicIsometries Q → QuaternionicIsometries Q))
    simpa only [Function.comp_def, mapPair_mul] using
      (hf.fst.compCM hg.fst).prodMk (hg.snd.compCM hf.snd)

instance [LocallyCompactSpace M] : IsTopologicalGroup (QuaternionicIsometries Q) := {}

theorem continuous_action [LocallyCompactSpace M] :
    Continuous (fun p : QuaternionicIsometries Q × M => p.1 • p.2) := by
  exact continuous_eval.comp
    (((continuous_mapPair Q).comp continuous_fst).fst.prodMk continuous_snd)

instance [LocallyCompactSpace M] : ContinuousSMul (QuaternionicIsometries Q) M :=
  ⟨continuous_action Q⟩

/-- A jointly continuous action of a topological group by the actual
quaternionic isometries gives a continuous homomorphism into their
compact-open topological group. Inverse continuity comes from the source
group, not an additional assumption about the action. -/
theorem continuous_representation_of_action
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : G →* QuaternionicIsometries Q)
    (hρ : Continuous (fun p : G × M => ρ p.1 • p.2)) : Continuous ρ := by
  apply (mapPair_isEmbedding Q).isInducing.continuous_iff.mpr
  have hforward : Continuous (fun t : G => (mapPair Q (ρ t)).1) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hρ
  have hbackward : Continuous (fun t : G => (mapPair Q (ρ t)).2) := by
    have h := hforward.comp continuous_inv
    simpa only [Function.comp_def, map_inv, mapPair_inv] using h
  exact hforward.prodMk hbackward

/-- The actual identity component, as a subgroup of the constructed
topological quaternionic isometry group. -/
def identityComponent [LocallyCompactSpace M] : Subgroup (QuaternionicIsometries Q) :=
  Subgroup.connectedComponentOfOne (QuaternionicIsometries Q)

theorem representation_mem_identityComponent [LocallyCompactSpace M]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [PreconnectedSpace G]
    (ρ : G →* QuaternionicIsometries Q)
    (hρ : Continuous (fun p : G × M => ρ p.1 • p.2)) (t : G) :
    ρ t ∈ identityComponent Q := by
  have hc := (continuous_representation_of_action Q ρ hρ).mapsTo_connectedComponent (1 : G)
  have ht : t ∈ connectedComponent (1 : G) := by
    rw [preconnectedSpace_iff_connectedComponent.mp inferInstance]
    trivial
  simpa only [map_one] using hc ht

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryTopology
