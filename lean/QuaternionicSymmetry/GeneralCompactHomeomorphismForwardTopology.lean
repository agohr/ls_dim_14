import QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphismTopology
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-! On a compact Hausdorff space, a family of homeomorphisms continuous in
the forward compact-open topology also has continuously varying inverses.
The proof uses the properness of the product projection, not an assumed
topological-group structure on the family. -/

namespace QuaternionicSymmetry.GeneralCompactHomeomorphismForwardTopology

open GeneralHolomorphicDistributionAutomorphisms
open GeneralHolomorphicDistributionAutomorphismTopology Topology
open scoped Manifold ContDiff
noncomputable section

variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [ChartedSpace V Z] [IsManifold 𝓘(ℂ,V) ∞ Z]
  (D : Z → Submodule ℂ V)

/-- The ordinary forward compact-open map on the actual automorphism carrier. -/
def forwardMap (f : Automorphisms D) : C(Z,Z) := (mapPair D f).1

/-- The ordinary forward compact-open topology, independent of the project's
forward/inverse pair topology. -/
def forwardTopology : TopologicalSpace (Automorphisms D) :=
  TopologicalSpace.induced (forwardMap D) inferInstance

private theorem forwardMap_injective : Function.Injective (forwardMap D) := by
  intro f g h
  apply Subtype.ext
  apply Diffeomorph.ext
  intro z
  exact congrArg (fun k : C(Z,Z) => k z) h

private theorem backward_continuous_in_forwardTopology :
    @Continuous (Automorphisms D) C(Z,Z) (forwardTopology D) inferInstance
      (fun f => (mapPair D f).2) := by
  letI : TopologicalSpace (Automorphisms D) := forwardTopology D
  have hForward : Continuous (forwardMap D) := continuous_induced_dom
  have hEmb : IsEmbedding (forwardMap D) :=
    ⟨⟨rfl⟩, forwardMap_injective D⟩
  letI : T2Space (Automorphisms D) := hEmb.t2Space
  let F : Automorphisms D × Z → Automorphisms D × Z :=
    fun p => (p.1, p.1.1 p.2)
  let R : Automorphisms D × Z → Automorphisms D × Z :=
    fun p => (p.1, p.1.1.symm p.2)
  have hF : Continuous F := by
    dsimp [F]
    exact continuous_fst.prodMk
      (continuous_eval.comp ((hForward.comp continuous_fst).prodMk continuous_snd))
  have hProper : IsProperMap F := by
    apply isProperMap_of_comp_of_t2 hF continuous_fst
    exact isProperMap_fst_of_compactSpace
  have hBij : Function.Bijective F := by
    constructor
    · intro p q h
      have h₁ := congrArg (fun x : Automorphisms D × Z => x.1) h
      change p.1 = q.1 at h₁
      dsimp [F] at h
      cases p with
      | mk p z =>
        cases q with
        | mk q w =>
          dsimp [F] at h₁ h
          subst q
          have h₂ : p.1 z = p.1 w := congrArg Prod.snd h
          congr 1
          exact p.1.injective h₂
    · intro p
      refine ⟨R p, ?_⟩
      cases p with
      | mk f z =>
        apply Prod.ext <;> simp [F, R]
  have hHomeo : IsHomeomorph F :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨hF, hProper.isClosedMap, hBij⟩
  obtain ⟨_, g, _, hRight, hg⟩ :=
    isHomeomorph_iff_exists_inverse.mp hHomeo
  have hR : Continuous R := by
    have hFR : ∀ p, F (R p) = p := by
      intro p
      cases p with
      | mk f z =>
        apply Prod.ext <;> simp [F, R]
    have heq : R = g := by
      funext p
      apply hBij.1
      exact (hFR p).trans (hRight p).symm
    exact heq ▸ hg
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h := continuous_snd.comp hR
  simpa only [Function.comp_def, R] using h

/-- For compact Hausdorff twistor spaces, the project's forward/inverse
compact-open topology equals the usual forward compact-open topology. -/
theorem pairTopology_eq_forwardTopology :
    (inferInstance : TopologicalSpace (Automorphisms D)) = forwardTopology D := by
  apply le_antisymm
  · exact (continuous_fst.comp (continuous_mapPair D)).le_induced
  · letI : TopologicalSpace (Automorphisms D) := forwardTopology D
    have hf : Continuous (forwardMap D) := continuous_induced_dom
    have hb := backward_continuous_in_forwardTopology D
    exact (hf.prodMk hb).le_induced

end
end QuaternionicSymmetry.GeneralCompactHomeomorphismForwardTopology
