import QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphisms
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction

/-! The independent compact-open forward/inverse topology on actual
holomorphic distribution automorphisms, with continuous multiplication,
inversion and evaluation. No Lie structure is assumed or manufactured. -/

namespace QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphismTopology

open GeneralHolomorphicDistributionAutomorphisms Topology
open scoped Manifold ContDiff
noncomputable section

variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace Z] [ChartedSpace V Z] [IsManifold 𝓘(ℂ,V) ∞ Z]
  (D : Z → Submodule ℂ V)

def mapPair (f : Automorphisms D) : C(Z,Z) × C(Z,Z) :=
  (⟨f.1, f.1.continuous⟩, ⟨f.1.symm, f.1.symm.continuous⟩)

instance : TopologicalSpace (Automorphisms D) :=
  TopologicalSpace.induced (mapPair D) inferInstance

theorem mapPair_injective : Function.Injective (mapPair D) := by
  intro f g h
  apply Subtype.ext
  apply Diffeomorph.ext
  intro z
  exact congrArg (fun p : C(Z,Z) × C(Z,Z) => p.1 z) h

theorem mapPair_isEmbedding : IsEmbedding (mapPair D) :=
  ⟨⟨rfl⟩, mapPair_injective D⟩

theorem continuous_mapPair : Continuous (mapPair D) :=
  (mapPair_isEmbedding D).continuous

instance [T2Space Z] : T2Space (Automorphisms D) :=
  (mapPair_isEmbedding D).t2Space

theorem mapPair_inv (f : Automorphisms D) :
    mapPair D f⁻¹ = (mapPair D f).swap := by
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro z <;> rfl

theorem mapPair_mul (f g : Automorphisms D) :
    mapPair D (f*g) =
      ((mapPair D f).1.comp (mapPair D g).1,
       (mapPair D g).2.comp (mapPair D f).2) := by
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro z <;> rfl

instance : ContinuousInv (Automorphisms D) where
  continuous_inv := by
    apply (mapPair_isEmbedding D).isInducing.continuous_iff.mpr
    simpa only [Function.comp_def, mapPair_inv] using
      continuous_swap.comp (continuous_mapPair D)

instance [LocallyCompactSpace Z] : ContinuousMul (Automorphisms D) where
  continuous_mul := by
    apply (mapPair_isEmbedding D).isInducing.continuous_iff.mpr
    have hf := (continuous_mapPair D).comp
      (continuous_fst : Continuous (Prod.fst : Automorphisms D ×
        Automorphisms D → Automorphisms D))
    have hg := (continuous_mapPair D).comp
      (continuous_snd : Continuous (Prod.snd : Automorphisms D ×
        Automorphisms D → Automorphisms D))
    simpa only [Function.comp_def, mapPair_mul] using
      (hf.fst.compCM hg.fst).prodMk (hg.snd.compCM hf.snd)

instance [LocallyCompactSpace Z] : IsTopologicalGroup (Automorphisms D) := {}

theorem continuous_action [LocallyCompactSpace Z] :
    Continuous (fun p : Automorphisms D × Z => p.1 • p.2) :=
  continuous_eval.comp
    (((continuous_mapPair D).comp continuous_fst).fst.prodMk continuous_snd)

theorem continuous_representation_of_action
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : G →* Automorphisms D)
    (hρ : Continuous (fun p : G × Z => ρ p.1 • p.2)) : Continuous ρ := by
  apply (mapPair_isEmbedding D).isInducing.continuous_iff.mpr
  have hf : Continuous (fun t : G => (mapPair D (ρ t)).1) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hρ
  have hb : Continuous (fun t : G => (mapPair D (ρ t)).2) := by
    have h := hf.comp continuous_inv
    simpa only [Function.comp_def, map_inv, mapPair_inv] using h
  exact hf.prodMk hb

end
end QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphismTopology
