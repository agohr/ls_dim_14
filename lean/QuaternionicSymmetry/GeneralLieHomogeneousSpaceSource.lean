import QuaternionicSymmetry.GeneralClosedSubgroupLieSource
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
General source-facing homogeneous-space theorem: Lee, *Introduction to
Smooth Manifolds*, 2nd ed., Theorem 21.17, printed pp.551–552 (PDF
pp.568–569). For an actual finite-dimensional real Lie group G and an
actual closed subgroup H with its Lee 20.12 embedded Lie atlas, the genuine
topological coset quotient G/H inherits a smooth real manifold atlas;
the quotient map is a smooth submersion, the left action is smooth, and
dim(G/H)+dim(H)=dim(G). No invariant metric is part of this theorem.
-/

namespace QuaternionicSymmetry.GeneralLieHomogeneousSpaceSource

open Manifold Topology
open scoped Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The canonical group action on the actual left-coset quotient. -/
def leftCosetAction {G : Type} [Group G] (H : Subgroup G)
    (u : G) (q : G ⧸ H) : G ⧸ H := by
  letI : MulAction.QuotientAction G H := MulAction.left_quotientAction H
  letI : MulAction G (G ⧸ H) := MulAction.quotient G H
  exact u • q

/-- Every output of Lee 21.17 is expressed on actual Mathlib cosets,
with true derivative surjectivity and the canonical left action. -/
structure SmoothQuotientAtlas
    (G : Type) [Group G] [TopologicalSpace G]
    (d : ℕ) [ChartedSpace (RModel d) G]
    (H : Subgroup G) (e q : ℕ) where
  charts : ChartedSpace (RModel q) (G ⧸ H)
  manifold : letI := charts
    IsManifold 𝓘(ℝ, RModel q) ∞ (G ⧸ H)
  quotientSmooth : letI := charts
    ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, RModel q) ∞
      (fun u : G => (u : G ⧸ H))
  quotientSubmersive : letI := charts
    ∀ u : G, Function.Surjective
      (mfderiv 𝓘(ℝ, RModel d) 𝓘(ℝ, RModel q)
        (fun v : G => (v : G ⧸ H)) u)
  actionSmooth : letI := charts
    ContMDiff (𝓘(ℝ, RModel d).prod 𝓘(ℝ, RModel q))
      𝓘(ℝ, RModel q) ∞
      (fun p : G × (G ⧸ H) => leftCosetAction H p.1 p.2)
  dimension : q + e = d

/-- General Lee 21.17 input. The actual closed subgroup and its real
embedded Lie atlas appear explicitly; the source returns only the
quotient geometry and the dimension subtraction formula. -/
def LeeHomogeneousSpaceTheorem : Prop :=
  ∀ {G : Type} [Group G] [TopologicalSpace G] [T2Space G]
    [SecondCountableTopology G]
    (d : ℕ) [ChartedSpace (RModel d) G]
    [IsManifold 𝓘(ℝ, RModel d) ∞ G]
    [LieGroup 𝓘(ℝ, RModel d) ∞ G]
    (H : Subgroup G) (_hClosed : IsClosed (H : Set G))
    (e : ℕ) (_hAtlas : GeneralClosedSubgroupLieSource.EmbeddedRealLieAtlas
      (RModel d) H G H.subtype e),
      ∃ q : ℕ, Nonempty (SmoothQuotientAtlas G d H e q)

end
end QuaternionicSymmetry.GeneralLieHomogeneousSpaceSource
