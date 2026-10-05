import QuaternionicSymmetry.SelectedTorusEmbeddedLieAtlas
import QuaternionicSymmetry.ContinuousLieHomSmooth
import QuaternionicSymmetry.ComplexTorusLieGroup
import QuaternionicSymmetry.ComplexLieRealCompanion

/-! The literal unit-circle coordinate inclusion of the selected compact
torus is real smooth in its BG-L3 atlas and the existing complex torus atlas. -/

namespace QuaternionicSymmetry.SelectedTorusCompactInclusionSmooth

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ContinuousLieHomSmooth ComplexLieRealCompanion
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

theorem compactInclusion_continuous :
    Continuous (compactInclusion r) := by
  apply continuous_pi
  intro i
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun t : Fin r → Circle => (t i : ℂ))
    exact continuous_subtype_val.comp (continuous_apply i)
  · change Continuous (fun t : Fin r → Circle => (((t i)⁻¹ : Circle) : ℂ))
    have hi : Continuous (fun t : Fin r → Circle => (t i : ℂ)) :=
      continuous_subtype_val.comp (continuous_apply i)
    simpa only [Circle.coe_inv_eq_conj] using
      Complex.continuous_conj.comp hi

theorem compactInclusion_smooth
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
    ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ, Fin r → ℂ) ∞
      (compactInclusion r) := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.lieGroup
  letI : T2Space (ComplexTorus r) :=
    (ComplexTorusHolomorphicStructure.torusVal_isOpenEmbedding r).t2Space
  letI : SecondCountableTopology (ComplexTorus r) :=
    (ComplexTorusHolomorphicStructure.torusVal_isOpenEmbedding r).secondCountableTopology
  letI : IsManifold 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realManifold
  letI : LieGroup 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realLieGroup
  exact continuous_hom_smooth (compactInclusion r)
    hClosed hImm hLee (compactInclusion_continuous (r := r))

end
end QuaternionicSymmetry.SelectedTorusCompactInclusionSmooth
