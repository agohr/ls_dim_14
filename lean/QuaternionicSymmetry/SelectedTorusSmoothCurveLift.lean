import QuaternionicSymmetry.SelectedTorusEmbeddedLieAtlas
import QuaternionicSymmetry.InjectiveLieHomImmersion

/-! Every smooth curve whose image lies in the SAME selected torus lifts
smoothly through its actual embedded Lie atlas. This is BG-D3 applied to
the literal selected embedding, with differential injectivity derived
from BG-L6; no Lie subgroup inverse API is assumed. -/

namespace QuaternionicSymmetry.SelectedTorusSmoothCurveLift

open CompactLieTorusInputs GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open SelectedTorusEmbeddedLieAtlas InjectiveLieHomImmersion
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r d : ℕ} (T : TorusEmbedding G r)
  (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d)
  (c : ℝ → G) (hcRange : ∀ s, c s ∈ T.hom.range)

def liftCurve : ℝ → Fin r → Circle :=
  fun s => Classical.choose (hcRange s)

theorem liftCurve_map (s : ℝ) :
    T.hom (liftCurve T c hcRange s) = c s :=
  Classical.choose_spec (hcRange s)

theorem liftCurve_smooth
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hc : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,V) ∞ c) :
    letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin d → ℝ) ∞
      (liftCurve T c hcRange) := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.lieGroup
  letI : T2Space (Fin r → Circle) := inferInstance
  letI : CompactSpace (Fin r → Circle) := inferInstance
  letI : SecondCountableTopology (Fin r → Circle) :=
    ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℝ) _
  have hT : ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ∞ T.hom :=
    selected_hom_smooth T g
  have hDeriv : ∀ t : Fin r → Circle,
      Function.Injective
        (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) T.hom t) := by
    intro t
    exact smooth_injective_hom_immersion T.hom hImm hT T.injective_hom t
  apply hLee (E := ℝ) (F := Fin d → ℝ) (V := V)
    T.hom (liftCurve T c hcRange)
  · exact g.smoothEmbedding.isEmbedding
  · exact hT
  · exact hDeriv
  · simpa only [Function.comp_def, liftCurve_map] using hc

end
end QuaternionicSymmetry.SelectedTorusSmoothCurveLift
