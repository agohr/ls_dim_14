import QuaternionicSymmetry.SelectedTorusCompactDerivativePureImaginary
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! The actual BG-L3 selected torus atlas dimension is at most its
written number of circle coordinates. The proof uses the injective
derivative of the literal compact inclusion and the checked unit-circle
real-velocity constraint. -/

namespace QuaternionicSymmetry.SelectedTorusAtlasDimensionUpper

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusCompactInclusionImmersion
open SelectedTorusCompactDerivativePureImaginary
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open TorusLaurentRepresentation
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

theorem selected_atlas_dim_le_rank
    (T : TorusEmbedding G r)
    (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    d ≤ r := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  let A : (Fin d → ℝ) →ₗ[ℝ] (Fin r → ℂ) :=
    (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin r → ℂ)
      (compactInclusion r) 1).toLinearMap
  let imMap : (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℝ) := {
    toFun z i := (z i).im
    map_add' := by intros; funext i; simp
    map_smul' := by intros; funext i; simp [Complex.smul_im] }
  have hA : Function.Injective A :=
    compactInclusion_mfderiv_injective T g hImm hClosed hLee
  have hIA : Function.Injective (imMap.comp A) := by
    intro u v huv
    apply hA
    apply funext
    intro i
    apply Complex.ext
    · have hu := compactInclusion_derivative_re_zero T g hClosed hImm hLee u i
      have hv := compactInclusion_derivative_re_zero T g hClosed hImm hLee v i
      simpa [A] using hu.trans hv.symm
    · exact congrFun huv i
  have hdim := LinearMap.finrank_le_finrank_of_injective hIA
  simpa using hdim

end
end QuaternionicSymmetry.SelectedTorusAtlasDimensionUpper
