import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Precisely sourced general compact Lie-group inputs. The torus is an
actual injective continuous homomorphism from a product of circles, and
maximality is inclusion maximality among such subgroups. No manifold
classification or quaternionic-preservation conclusion is included.

BG-L1/BG-L2: published Knapp corollaries; exact locators and external
derivations are registered in Textbooks/SOURCES_AND_STATUS.md under
"Precisely located compact Lie-group background". Contracts unchanged.
-/

namespace QuaternionicSymmetry.CompactLieTorusInputs

open scoped Manifold ContDiff
noncomputable section
universe uTorus vTorus

variable (G : Type*) [Group G] [TopologicalSpace G]

/-- A concrete compact torus in the given topological group. For a
Hausdorff target its injective continuous parametrization is an embedding. -/
structure TorusEmbedding (r : ℕ) where
  hom : (Fin r → Circle) →* G
  continuous_hom : Continuous hom
  injective_hom : Function.Injective hom

theorem TorusEmbedding.isClosedEmbedding [T2Space G] {r : ℕ}
    (T : TorusEmbedding G r) : Topology.IsClosedEmbedding T.hom :=
  T.continuous_hom.isClosedEmbedding T.injective_hom

/-- Coordinate inclusion of standard tori, with unused coordinates one. -/
def coordinateInclusion {r s : ℕ} (_h : r ≤ s) :
    (Fin r → Circle) →* (Fin s → Circle) where
  toFun t i := if hi : i.val < r then t ⟨i.val,hi⟩ else 1
  map_one' := by funext i; dsimp; split_ifs <;> rfl
  map_mul' t u := by funext i; dsimp; split_ifs <;> simp

theorem coordinateInclusion_continuous {r s : ℕ} (h : r ≤ s) :
    Continuous (coordinateInclusion h) := by
  apply continuous_pi
  intro i
  change Continuous (fun t : Fin r → Circle =>
    if hi : i.val < r then t ⟨i.val,hi⟩ else 1)
  split_ifs <;> fun_prop

theorem coordinateInclusion_injective {r s : ℕ} (h : r ≤ s) :
    Function.Injective (coordinateInclusion h) := by
  intro t u htu
  funext i
  have hi := congrFun htu (⟨i.val,lt_of_lt_of_le i.isLt h⟩ : Fin s)
  simpa [coordinateInclusion,i.isLt] using hi

def TorusEmbedding.restrictRank {r s : ℕ} (T : TorusEmbedding G s)
    (h : r ≤ s) : TorusEmbedding G r where
  hom := T.hom.comp (coordinateInclusion h)
  continuous_hom := T.continuous_hom.comp (coordinateInclusion_continuous h)
  injective_hom := T.injective_hom.comp (coordinateInclusion_injective h)

def IsTorusSubgroup (S : Subgroup G) : Prop :=
  ∃ r : ℕ, ∃ T : TorusEmbedding G r, T.hom.range = S

def TorusEmbedding.IsMaximal {r : ℕ} (T : TorusEmbedding G r) : Prop :=
  ∀ S : Subgroup G, IsTorusSubgroup G S → T.hom.range ≤ S → S = T.hom.range

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [ChartedSpace V G]

/-- BG-L1 on this actual Lie-group model, including the positive-rank
corollary of Knapp Proposition 4.30. All source hypotheses remain
explicit inside the universal statement. -/
def MaximalTorusExistenceOnModel : Prop :=
  ∀ [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ,V) ∞ G]
    [LieGroup 𝓘(ℝ,V) ∞ G] [CompactSpace G] [ConnectedSpace G]
    [T2Space G] [SecondCountableTopology G],
    0 < Module.finrank ℝ V →
      ∃ r : ℕ, 0 < r ∧ ∃ T : TorusEmbedding G r, T.IsMaximal G

/-- BG-L2's dimension conclusion: a compact connected rank-one group
has dimension at most three. Rank is measured by a genuine maximal
circle subgroup, not by an arbitrary numerical field. -/
def CompactRankOneDimensionOnModel : Prop :=
  ∀ [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ,V) ∞ G]
    [LieGroup 𝓘(ℝ,V) ∞ G] [CompactSpace G] [ConnectedSpace G]
    [T2Space G] [SecondCountableTopology G],
    ∀ T : TorusEmbedding G 1, T.IsMaximal G → Module.finrank ℝ V ≤ 3

theorem exists_rank_two_torus_of_dimension_gt_three
    [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ,V) ∞ G]
    [LieGroup 𝓘(ℝ,V) ∞ G] [CompactSpace G] [ConnectedSpace G]
    [T2Space G] [SecondCountableTopology G]
    (hTorus : MaximalTorusExistenceOnModel (V := V) G)
    (hRankOne : CompactRankOneDimensionOnModel (V := V) G)
    (hdim : 3 < Module.finrank ℝ V) :
    ∃ r : ℕ, 2 ≤ r ∧ Nonempty (TorusEmbedding G r) := by
  obtain ⟨r,hr,T,hT⟩ := hTorus (by omega)
  have hne : r ≠ 1 := by
    intro h
    subst r
    have hbound := hRankOne T hT
    omega
  exact ⟨r,by omega,⟨T⟩⟩

theorem exists_two_torus_of_dimension_gt_three
    [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ,V) ∞ G]
    [LieGroup 𝓘(ℝ,V) ∞ G] [CompactSpace G] [ConnectedSpace G]
    [T2Space G] [SecondCountableTopology G]
    (hTorus : MaximalTorusExistenceOnModel (V := V) G)
    (hRankOne : CompactRankOneDimensionOnModel (V := V) G)
    (hdim : 3 < Module.finrank ℝ V) : Nonempty (TorusEmbedding G 2) := by
  obtain ⟨r,hr,⟨T⟩⟩ :=
    exists_rank_two_torus_of_dimension_gt_three G hTorus hRankOne hdim
  exact ⟨T.restrictRank G hr⟩

/-- Universally quantified BG-L1, allowing application to the Lie atlas
constructed by the isometry theorem rather than a supplied atlas. -/
def MaximalTorusSource : Prop :=
  ∀ (V : Type uTorus) (G : Type vTorus)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Group G] [TopologicalSpace G] [ChartedSpace V G],
    MaximalTorusExistenceOnModel (V := V) G

/-- Universally quantified BG-L2, on genuine maximal circle subgroups. -/
def CompactRankOneDimensionSource : Prop :=
  ∀ (V : Type uTorus) (G : Type vTorus)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Group G] [TopologicalSpace G] [ChartedSpace V G],
    CompactRankOneDimensionOnModel (V := V) G

end
end QuaternionicSymmetry.CompactLieTorusInputs
