import QuaternionicSymmetry.SelectedTorusCompactInclusionSmooth
import QuaternionicSymmetry.InjectiveLieHomImmersion

/-! The literal compact inclusion is a real immersion in the SAME
selected-torus atlas. In particular its identity differential has
rank equal to the selected atlas dimension `d`. -/

namespace QuaternionicSymmetry.SelectedTorusCompactInclusionImmersion

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusCompactInclusionSmooth
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open InjectiveLieHomImmersion ComplexLieRealCompanion
open ComplexTorusLieGroup TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r d : ℕ} (T : TorusEmbedding G r)
  (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d)

theorem compactInclusion_injective :
    Function.Injective (compactInclusion r) := by
  intro t u h
  funext i
  apply unitSphereToUnits_injective
  exact congrFun h i

theorem compactInclusion_mfderiv_injective
    (hImm : LeeEquivariantImmersionTheorem)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
    Function.Injective
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin r → ℂ)
        (compactInclusion r) 1) := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.lieGroup
  letI : T2Space (ComplexTorus r) :=
    (ComplexTorusHolomorphicStructure.torusVal_isOpenEmbedding r).t2Space
  letI : SecondCountableTopology (ComplexTorus r) :=
    (ComplexTorusHolomorphicStructure.torusVal_isOpenEmbedding r).secondCountableTopology
  letI : IsManifold 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realManifold
  letI : LieGroup 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realLieGroup
  exact smooth_injective_hom_immersion
    (compactInclusion r) hImm
    (compactInclusion_smooth T g hClosed hImm hLee)
    (compactInclusion_injective (r := r)) 1

end
end QuaternionicSymmetry.SelectedTorusCompactInclusionImmersion
