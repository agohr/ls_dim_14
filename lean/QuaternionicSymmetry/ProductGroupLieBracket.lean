import QuaternionicSymmetry.SmoothLieHomDerivativeBracket

/-! The genuine tangent Lie bracket of a product Lie group is componentwise.
This follows from the actual smooth projection homomorphisms and their
literal derivatives, without assigning a replacement product bracket. -/

namespace QuaternionicSymmetry.ProductGroupLieBracket

open SmoothLieHomDerivativeBracket
open scoped Manifold ContDiff
noncomputable section

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(𝕜,E) ∞ G] [LieGroup 𝓘(𝕜,E) ∞ G]
  [Group H] [TopologicalSpace H] [ChartedSpace F H]
  [IsManifold 𝓘(𝕜,F) ∞ H] [LieGroup 𝓘(𝕜,F) ∞ H]
  [ENat.LEInfty (minSmoothness 𝕜 3)]

local instance productCharts : ChartedSpace (E × F) (G × H) :=
  prodChartedSpace E G F H

instance productSelfManifold : IsManifold 𝓘(𝕜,E × F) ∞ (G × H) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod G H

instance productSelfLieGroup : LieGroup 𝓘(𝕜,E × F) ∞ (G × H) := by
  rw [modelWithCornersSelf_prod]
  exact Prod.instLieGroup

theorem projection_fst_mfderiv (p : G × H) :
    mfderiv 𝓘(𝕜,E × F) 𝓘(𝕜,E) (MonoidHom.fst G H) p =
      ContinuousLinearMap.fst 𝕜 E F := by
  change mfderiv 𝓘(𝕜,E × F) 𝓘(𝕜,E) Prod.fst p = _
  rw [modelWithCornersSelf_prod, mfderiv_fst]
  rfl

theorem projection_snd_mfderiv (p : G × H) :
    mfderiv 𝓘(𝕜,E × F) 𝓘(𝕜,F) (MonoidHom.snd G H) p =
      ContinuousLinearMap.snd 𝕜 E F := by
  change mfderiv 𝓘(𝕜,E × F) 𝓘(𝕜,F) Prod.snd p = _
  rw [modelWithCornersSelf_prod, mfderiv_snd]
  rfl

theorem bracket_fst (u v : GroupLieAlgebra 𝓘(𝕜,E × F) (G × H)) :
    (⁅u,v⁆).1 = @Bracket.bracket (GroupLieAlgebra 𝓘(𝕜,E) G)
      (GroupLieAlgebra 𝓘(𝕜,E) G) inferInstance u.1 v.1 := by
  have hs : ContMDiff 𝓘(𝕜,E × F) 𝓘(𝕜,E) ∞ (MonoidHom.fst G H) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have h := mfderiv_map_lie (MonoidHom.fst G H) hs u v
  rw [projection_fst_mfderiv] at h
  exact h

theorem bracket_snd (u v : GroupLieAlgebra 𝓘(𝕜,E × F) (G × H)) :
    (⁅u,v⁆).2 = @Bracket.bracket (GroupLieAlgebra 𝓘(𝕜,F) H)
      (GroupLieAlgebra 𝓘(𝕜,F) H) inferInstance u.2 v.2 := by
  have hs : ContMDiff 𝓘(𝕜,E × F) 𝓘(𝕜,F) ∞ (MonoidHom.snd G H) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have h := mfderiv_map_lie (MonoidHom.snd G H) hs u v
  rw [projection_snd_mfderiv] at h
  exact h

theorem bracket_cross_eq_zero
    (v : GroupLieAlgebra 𝓘(𝕜,E) G) (w : GroupLieAlgebra 𝓘(𝕜,F) H) :
    @Bracket.bracket (GroupLieAlgebra 𝓘(𝕜,E × F) (G × H))
      (GroupLieAlgebra 𝓘(𝕜,E × F) (G × H)) inferInstance (v,0) (0,w) = 0 := by
  apply Prod.ext
  · exact (bracket_fst (𝕜 := 𝕜) (E := E) (F := F) (G := G) (H := H)
      (v,0) (0,w)).trans (lie_zero (M := GroupLieAlgebra 𝓘(𝕜,E) G) v)
  · exact (bracket_snd (𝕜 := 𝕜) (E := E) (F := F) (G := G) (H := H)
      (v,0) (0,w)).trans (zero_lie w)

end
end QuaternionicSymmetry.ProductGroupLieBracket
