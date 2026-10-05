import QuaternionicSymmetry.SelectedTorusAtlasDimensionExact
import QuaternionicSymmetry.SelectedTorusLieSpanDerivativeEquality
import QuaternionicSymmetry.InjectiveLieHomImmersion

/-! The intrinsic ambient Lie span of the SAME selected compact torus has
its written rank. The embedded atlas dimension, derivative injectivity and
equality of the curve span with the derivative range are all used on the
same parametrization; no maximality or dimension conclusion is assumed. -/

namespace QuaternionicSymmetry.SelectedTorusLieSpanDimension

open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open SelectedTorusEmbeddedLieAtlas SelectedTorusAtlasDimensionExact
open SelectedTorusLieSpanDerivativeEquality InjectiveLieHomImmersion
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r d : ℕ}

theorem finrank_torusLieSpan
    (T : TorusEmbedding G r)
    (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    Module.finrank ℝ (torusLieSpan (V := V) T) = r := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.lieGroup
  letI : SecondCountableTopology (Fin r → Circle) :=
    ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℝ) _
  have hInj := smooth_injective_hom_immersion T.hom hImm
    (selected_hom_smooth T g) T.injective_hom (1 : Fin r → Circle)
  rw [torusLieSpan_eq_derivative_range T g hImm hLee]
  have hdim := LinearMap.finrank_range_of_inj
    (f := (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) T.hom 1).toLinearMap) hInj
  calc
    _ = Module.finrank ℝ (Fin d → ℝ) := hdim
    _ = d := by simp
    _ = r := selected_atlas_dimension_eq_rank T g hClosed hImm hLee

theorem finrank_torusLieSpan_from_sources
    (T : TorusEmbedding G r)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    Module.finrank ℝ (torusLieSpan (V := V) T) = r := by
  obtain ⟨d, ⟨g⟩⟩ := exists_selected_embedded_atlas (V := V) T hClosed
  exact finrank_torusLieSpan T g hClosed hImm hLee

end
end QuaternionicSymmetry.SelectedTorusLieSpanDimension
