import QuaternionicSymmetry.ContinuousComplexLieHomRealSmooth
import QuaternionicSymmetry.InjectiveLieHomImmersion

/-! A faithful continuous complex Lie-group homomorphism is a real smooth
immersion, using BG-L3/L6/D3 internally. Holomorphicity is not inferred. -/

namespace QuaternionicSymmetry.ContinuousComplexLieHomImmersion

open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ContinuousComplexLieHomRealSmooth
open InjectiveLieHomImmersion ComplexLieRealCompanion
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

theorem continuous_injective_hom_real_immersion
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hf : Continuous f)
    (hInj : Function.Injective f) (x : G) :
    Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) := by
  letI : IsManifold 𝓘(ℝ,E) ∞ G := realManifold
  letI : IsManifold 𝓘(ℝ,F) ∞ H := realManifold
  letI : LieGroup 𝓘(ℝ,E) ∞ G := realLieGroup
  letI : LieGroup 𝓘(ℝ,F) ∞ H := realLieGroup
  exact continuous_injective_hom_immersion f hClosed hImm hLee hf hInj x

end
end QuaternionicSymmetry.ContinuousComplexLieHomImmersion
