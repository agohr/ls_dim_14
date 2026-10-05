import QuaternionicSymmetry.SelectedTorusCompactExponentialSmooth
import QuaternionicSymmetry.SelectedTorusCompactInclusionImmersion

/-! The coordinatewise exponential becomes smooth in the SAME BG-L3
selected compact-torus atlas. This is BG-D3 applied to the actual
embedded compact inclusion, whose immersion is already proved. -/

namespace QuaternionicSymmetry.SelectedTorusCompactExponentialLift

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusCompactInclusionSmooth
open SelectedTorusCompactInclusionImmersion
open SelectedTorusCompactExponentialSmooth
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

theorem circleExpPi_smooth_selected
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
    ContMDiff 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin d → ℝ) ∞
      (circleExpPi r) := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.lieGroup
  letI : T2Space (ComplexTorus r) :=
    (ComplexTorusHolomorphicStructure.torusVal_isOpenEmbedding r).t2Space
  letI : SecondCountableTopology (ComplexTorus r) :=
    (ComplexTorusHolomorphicStructure.torusVal_isOpenEmbedding r).secondCountableTopology
  letI : IsManifold 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realManifold
  letI : LieGroup 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realLieGroup
  letI : T2Space (Fin r → Circle) := inferInstance
  letI : CompactSpace (Fin r → Circle) := inferInstance
  letI : SecondCountableTopology (Fin r → Circle) :=
    ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℝ) _
  have hEmb : Topology.IsEmbedding (compactInclusion r) :=
    ((compactInclusion_continuous (r := r)).isClosedEmbedding
      (compactInclusion_injective (r := r))).isEmbedding
  have hInc := compactInclusion_smooth T g hClosed hImm hLee
  have hDeriv : ∀ t : Fin r → Circle,
      Function.Injective
        (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin r → ℂ)
          (compactInclusion r) t) := by
    intro t
    exact smooth_injective_hom_immersion (compactInclusion r)
      hImm hInc (compactInclusion_injective (r := r)) t
  exact hLee (E := Fin r → ℝ) (F := Fin d → ℝ)
    (V := Fin r → ℂ) (compactInclusion r) (circleExpPi r)
    hEmb hInc hDeriv (compactExp_smooth r)

end
end QuaternionicSymmetry.SelectedTorusCompactExponentialLift
