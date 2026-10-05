import QuaternionicSymmetry.ContinuousLieHomGraphAtlas
import QuaternionicSymmetry.ManifoldImmersionSmooth

/-! Automatic real smoothness of a continuous homomorphism between
finite-dimensional Lie groups, proved internally from the already
registered Lee closed-subgroup, equivariant-immersion, and embedded-
codomain theorems. The graph atlas is compared to the original source
atlas by the identity map; no new literature premise is used. -/

namespace QuaternionicSymmetry.ContinuousLieHomSmooth

open ContinuousLieHomGraphAtlas GeneralClosedSubgroupLieSource
open GeneralSmoothMapSource Topology
open scoped Manifold ContDiff
noncomputable section

variable {E F G H : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [SecondCountableTopology G]
  [ChartedSpace E G] [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [SecondCountableTopology H]
  [ChartedSpace F H] [IsManifold 𝓘(ℝ,F) ∞ H] [LieGroup 𝓘(ℝ,F) ∞ H]
  (f : G →* H)

private abbrev RModel (d : ℕ) := Fin d → ℝ

private abbrev GraphAtlas (d : ℕ) :=
  letI : ChartedSpace (E × F) (G × H) := prodChartedSpace E G F H
  EmbeddedRealLieAtlas (E × F) G (G × H) (graphHom f) d

theorem graph_to_original_smooth {d : ℕ}
    (g : GraphAtlas (E := E) (F := F) (G := G) (H := H) f d) :
    letI : ChartedSpace (E × F) (G × H) := prodChartedSpace E G F H
    letI : ChartedSpace (RModel d) G := g.charts
    ContMDiff 𝓘(ℝ,RModel d) 𝓘(ℝ,E) ∞ (id : G → G) := by
  letI : ChartedSpace (E × F) (G × H) := prodChartedSpace E G F H
  letI : IsManifold 𝓘(ℝ,E × F) ∞ (G × H) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod G H
  letI : ChartedSpace (RModel d) G := g.charts
  letI : IsManifold 𝓘(ℝ,RModel d) ∞ G := g.manifold
  have hGraph : ContMDiff 𝓘(ℝ,RModel d)
      (𝓘(ℝ,E).prod 𝓘(ℝ,F)) ∞ (graphHom f) := by
    simpa only [modelWithCornersSelf_prod] using
      ManifoldImmersionSmooth.smoothEmbedding_contMDiff g.smoothEmbedding
  simpa [graphHom, Function.id_def] using
    (contMDiff_fst.comp hGraph)

theorem original_to_graph_smooth
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    {d : ℕ}
    (g : GraphAtlas (E := E) (F := F) (G := G) (H := H) f d) :
    letI : ChartedSpace (E × F) (G × H) := prodChartedSpace E G F H
    letI : ChartedSpace (RModel d) G := g.charts
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,RModel d) ∞ (id : G → G) := by
  letI : ChartedSpace (E × F) (G × H) := prodChartedSpace E G F H
  letI : IsManifold 𝓘(ℝ,E × F) ∞ (G × H) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod G H
  letI : ChartedSpace (RModel d) G := g.charts
  letI : IsManifold 𝓘(ℝ,RModel d) ∞ G := g.manifold
  letI : LieGroup 𝓘(ℝ,RModel d) ∞ G := g.lieGroup
  have hπ := graph_to_original_smooth f g
  let a : SmoothLeftAction (RModel d) (RModel d) G G := {
    act x y := x * y
    one_act := one_mul
    mul_act := fun x y z => mul_assoc x y z
    smooth := contMDiff_mul 𝓘(ℝ,RModel d) ∞ }
  let b : SmoothLeftAction (RModel d) E G G := {
    act x y := x * y
    one_act := one_mul
    mul_act := fun x y z => mul_assoc x y z
    smooth := by
      exact (hπ.comp contMDiff_fst).mul contMDiff_snd }
  have hInj : ∀ x : G,
      Function.Injective
        (mfderiv 𝓘(ℝ,RModel d) 𝓘(ℝ,E) (id : G → G) x) := by
    apply hImm a b id
    · intro x y
      exact ⟨y * x⁻¹, by simp [a, mul_assoc]⟩
    · exact hπ
    · intro x y
      rfl
    · exact Function.injective_id
  apply hLee (E := E) (F := RModel d) (V := E)
    (id : G → G) (id : G → G)
  · exact IsEmbedding.id
  · exact hπ
  · exact hInj
  · exact contMDiff_id

theorem continuous_hom_smooth
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hf : Continuous f) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f := by
  letI : ChartedSpace (E × F) (G × H) := prodChartedSpace E G F H
  letI : IsManifold 𝓘(ℝ,E × F) ∞ (G × H) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod G H
  obtain ⟨d, ⟨g⟩⟩ := exists_graphLieAtlas (E := E) (F := F) f hClosed hf
  letI : ChartedSpace (RModel d) G := g.charts
  letI : IsManifold 𝓘(ℝ,RModel d) ∞ G := g.manifold
  have hGraph : ContMDiff 𝓘(ℝ,RModel d)
      (𝓘(ℝ,E).prod 𝓘(ℝ,F)) ∞ (graphHom f) := by
    simpa only [modelWithCornersSelf_prod] using
      ManifoldImmersionSmooth.smoothEmbedding_contMDiff g.smoothEmbedding
  have hInverse := original_to_graph_smooth f hImm hLee g
  have hComp := (contMDiff_snd.comp hGraph).comp hInverse
  simpa [graphHom, Function.id_def] using hComp

end
end QuaternionicSymmetry.ContinuousLieHomSmooth
