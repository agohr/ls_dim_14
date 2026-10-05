import QuaternionicSymmetry.CompactLieOneParameterSubgroup
import QuaternionicSymmetry.ContinuousLieHomSmooth
import QuaternionicSymmetry.EquivariantImmersionFromMathlib
import QuaternionicSymmetry.EmbeddedCodomainRestrictionFromMathlib

/-! Smoothness of the constructed one-parameter subgroup uses only the
retained closed-subgroup theorem; the two local immersion facts are proved. -/
namespace QuaternionicSymmetry.CompactLieOneParameterSmooth
open CompactLieOneParameterSubgroup GeneralClosedSubgroupLieSource
open scoped Manifold ContDiff
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]

theorem curve_smooth (hClosed : LeeClosedEmbeddingTheorem)
    (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (curve v) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  letI : ChartedSpace ℝ (Multiplicative ℝ) := inferInstanceAs (ChartedSpace ℝ ℝ)
  letI : IsManifold 𝓘(ℝ,ℝ) ∞ (Multiplicative ℝ) := inferInstanceAs (IsManifold 𝓘(ℝ,ℝ) ∞ ℝ)
  letI : LieGroup 𝓘(ℝ,ℝ) ∞ (Multiplicative ℝ) := {
    contMDiff_mul := by
      change ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × ℝ => p.1 + p.2)
      exact contMDiff_fst.add contMDiff_snd
    contMDiff_inv := by
      change ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun x : ℝ => -x)
      exact contMDiff_id.neg }
  exact ContinuousLieHomSmooth.continuous_hom_smooth (hom v) hClosed
    EquivariantImmersionFromMathlib.equivariantImmersion
    EmbeddedCodomainRestrictionFromMathlib.embeddedCodomainRestriction
    (continuous_hom v)

end
end QuaternionicSymmetry.CompactLieOneParameterSmooth
