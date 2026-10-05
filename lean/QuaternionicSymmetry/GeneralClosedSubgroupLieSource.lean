import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
Source-facing general closed-subgroup theorem, as a closed-embedding
corollary of Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem
20.12, printed pp.523–525 (PDF p.540). A continuous closed embedding of
an actual group into an actual finite-dimensional real Lie group identifies
it with a closed subgroup, which inherits an embedded real Lie atlas.

This is an explicit literature premise, not an axiom. Its output is an
actual Lean charted-space/manifold/Lie-group structure and a genuine smooth
embedding; it does not assume any model dimension or metric.
-/

namespace QuaternionicSymmetry.GeneralClosedSubgroupLieSource

open Manifold Topology
open scoped Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The geometric data supplied to a closed subgroup by Lee 20.12,
transported across the given closed group embedding. -/
structure EmbeddedRealLieAtlas
    (E A B : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace A] [Group A]
    [TopologicalSpace B] [Group B] [ChartedSpace E B]
    (f : A →* B) (d : ℕ) where
  charts : ChartedSpace (RModel d) A
  manifold : letI := charts
    IsManifold 𝓘(ℝ, RModel d) ∞ A
  lieGroup : letI := charts
    LieGroup 𝓘(ℝ, RModel d) ∞ A
  smoothEmbedding : letI := charts
    IsSmoothEmbedding 𝓘(ℝ, RModel d) 𝓘(ℝ, E) ∞ f

/-- General Lee 20.12 closed-subgroup input. The Hausdorff and second-
countable ambient hypotheses are explicit, as in the book's manifold
convention. The output dimension is existential. -/
def LeeClosedEmbeddingTheorem : Prop :=
  ∀ {E A B : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace A] [Group A] [IsTopologicalGroup A]
    [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
    [Group B] [ChartedSpace E B]
    [IsManifold 𝓘(ℝ,E) ∞ B] [LieGroup 𝓘(ℝ,E) ∞ B]
    (f : A →* B), IsClosedEmbedding f →
      ∃ d : ℕ, Nonempty (EmbeddedRealLieAtlas E A B f d)

end
end QuaternionicSymmetry.GeneralClosedSubgroupLieSource
