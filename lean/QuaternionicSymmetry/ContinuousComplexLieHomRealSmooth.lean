import QuaternionicSymmetry.ContinuousLieHomSmooth
import QuaternionicSymmetry.ComplexLieRealCompanion

/-! A continuous homomorphism of genuine finite-dimensional complex Lie
groups is real-C∞ in the same complex charts, using only the established
real closed-graph argument. This does not assert complex linearity of the
derivative. -/

namespace QuaternionicSymmetry.ContinuousComplexLieHomRealSmooth

open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ContinuousLieHomSmooth ComplexLieRealCompanion
open scoped Manifold ContDiff
noncomputable section

variable {E F G H : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [SecondCountableTopology G]
  [ChartedSpace E G] [IsManifold 𝓘(ℂ,E) ∞ G] [LieGroup 𝓘(ℂ,E) ∞ G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [SecondCountableTopology H]
  [ChartedSpace F H] [IsManifold 𝓘(ℂ,F) ∞ H] [LieGroup 𝓘(ℂ,F) ∞ H]
  (f : G →* H)

theorem continuous_hom_real_smooth
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hf : Continuous f) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f := by
  letI : IsManifold 𝓘(ℝ,E) ∞ G := realManifold
  letI : IsManifold 𝓘(ℝ,F) ∞ H := realManifold
  letI : LieGroup 𝓘(ℝ,E) ∞ G := realLieGroup
  letI : LieGroup 𝓘(ℝ,F) ∞ H := realLieGroup
  exact continuous_hom_smooth f hClosed hImm hLee hf

end
end QuaternionicSymmetry.ContinuousComplexLieHomRealSmooth
