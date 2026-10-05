import QuaternionicSymmetry.IdentityComponentTorusTangentSpan
import QuaternionicSymmetry.IdentityComponentLieBracketAgreement

/-! The BG-L1 maximal-torus real centralizer statement on the connected
component transfers internally to the full Lie algebra, with its literal
topological group and inherited open-component atlas. -/

namespace QuaternionicSymmetry.IdentityComponentTorusSelfCentralizingFull

open IdentityComponentLie CompactLieTorusMaximalTransfer
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open IdentityComponentTorusTangentSpan IdentityComponentLieBracketAgreement
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V] [ENat.LEInfty (minSmoothness ℝ 3)]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace V G] [LieGroup 𝓘(ℝ,V) ∞ G]

theorem full_torus_selfCentralizing_of_component
    {r : ℕ} (T : TorusEmbedding G r)
    (hAb : letI := IdentityComponentLie.charts V G
      letI := IdentityComponentLie.lieGroup V G
      ∀ x ∈ torusLieSpan (V := V) (G := Component G) (liftToComponent G T),
        ∀ y ∈ torusLieSpan (V := V) (G := Component G) (liftToComponent G T),
          (⁅x,y⁆ : GroupLieAlgebra 𝓘(ℝ,V) (Component G)) = 0)
    (hSelf : letI := IdentityComponentLie.charts V G
      letI := IdentityComponentLie.lieGroup V G
      ∀ x : GroupLieAlgebra 𝓘(ℝ,V) (Component G),
        (∀ y ∈ torusLieSpan (V := V) (G := Component G) (liftToComponent G T),
          ⁅x,y⁆ = 0) →
        x ∈ torusLieSpan (V := V) (G := Component G) (liftToComponent G T)) :
    (∀ x ∈ torusLieSpan (V := V) (G := G) T,
      ∀ y ∈ torusLieSpan (V := V) (G := G) T,
        (⁅x,y⁆ : GroupLieAlgebra 𝓘(ℝ,V) G) = 0) ∧
    (∀ x : GroupLieAlgebra 𝓘(ℝ,V) G,
      (∀ y ∈ torusLieSpan (V := V) (G := G) T, ⁅x,y⁆ = 0) →
        x ∈ torusLieSpan (V := V) (G := G) T) := by
  letI := IdentityComponentLie.charts V G
  letI := IdentityComponentLie.lieGroup V G
  have hSpan := torusLieSpan_liftToComponent_eq (V := V) T
  constructor
  · intro x hx y hy
    have hxC : x ∈ torusLieSpan (V := V) (G := Component G)
        (liftToComponent G T) := by rw [hSpan]; exact hx
    have hyC : y ∈ torusLieSpan (V := V) (G := Component G)
        (liftToComponent G T) := by rw [hSpan]; exact hy
    exact (component_bracket_eq_full (V := V) (G := G) x y).symm.trans
      (hAb x hxC y hyC)
  · intro x hx
    have hxc : x ∈ torusLieSpan (V := V) (G := Component G)
        (liftToComponent G T) := by
      apply hSelf x
      intro y hy
      have hyF : y ∈ torusLieSpan (V := V) (G := G) T := by
        rw [← hSpan]
        exact hy
      exact (component_bracket_eq_full (V := V) (G := G) x y).trans (hx y hyF)
    rw [← hSpan]
    exact hxc

end
end QuaternionicSymmetry.IdentityComponentTorusSelfCentralizingFull
