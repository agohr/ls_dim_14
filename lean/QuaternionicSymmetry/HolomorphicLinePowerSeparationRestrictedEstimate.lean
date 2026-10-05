import QuaternionicSymmetry.HolomorphicLinePowerSeparationFiniteFibers
import QuaternionicSymmetry.HolomorphicLineFiniteSectionsSource

/-! The existing compact restricted-section estimate needs only the
finite-fiber consequence of power-section ratio separation, not the
stronger `AmpleCore` structure of the whole intrinsic line. -/

namespace QuaternionicSymmetry.HolomorphicLinePowerSeparationRestrictedEstimate
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreCompleteRestriction
open HolomorphicLinePowerSeparationFiniteFibers
open HolomorphicLineFiniteSectionsSource
open HolomorphicFiniteMapDimensionSource
open HolomorphicAnalyticSubsetFiniteSource
open HolomorphicSeparatedFiniteFibersSource
open scoped Manifold ContDiff
noncomputable section

variable {B B' F F' : Type}
  [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
  [CompactSpace B] [Nonempty B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
  [TopologicalSpace B'] [T2Space B'] [SecondCountableTopology B']
  [CompactSpace B'] [Nonempty B']
  [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  [ChartedSpace F' B'] [IsManifold 𝓘(ℂ,F') ∞ B']

theorem restricted_section_finrank_bound_of_powerRatioSeparates
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (L : LineCore.{0} (B := B) 𝓘(ℂ,F))
    (f : B' → B) (hf : ContMDiff 𝓘(ℂ,F') 𝓘(ℂ,F) ∞ f)
    (hGen : GloballyGenerated 𝓘(ℂ,F) L)
    (k : ℕ) (hSep : PowerRatioSeparates L k)
    (hLiteral : SeparatedCompactAnalyticSubsetFiniteTheorem.{0,0})
    (hDim : FiniteHolomorphicMapDimensionTheorem.{0,0})
    (hfInj : Function.Injective f) :
    Module.finrank ℂ F' + 1 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,F')
        (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf)) := by
  obtain ⟨d, ⟨b⟩⟩ := exists_nonempty_section_basis hFinite L hGen
  let R := pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf
  let hR : GloballyGenerated 𝓘(ℂ,F') R :=
    globallyGenerated_pullback 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf hGen
  obtain ⟨e, ⟨c⟩⟩ := exists_nonempty_section_basis hFinite R hR
  have hAmbient : ∀ p : ComplexProjectiveTopology.Space d,
      ((projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen) ⁻¹' {p}).Finite := by
    intro p
    exact finiteFibers_of_powerRatioSeparates L
      (separatedCompactProjectiveFiber_of_analyticSubset hLiteral)
      k hSep d b hGen p
  have hFibers : ∀ q : ComplexProjectiveTopology.Space e,
      ((projectiveEvaluationOfGenerated 𝓘(ℂ,F') R e c hR) ⁻¹' {q}).Finite := by
    intro q
    exact completeRestrictedMap_finiteFibers_of_ambient
      𝓘(ℂ,F) 𝓘(ℂ,F') L f hf d b hGen e c hfInj hAmbient q
  exact section_finrank_bound_of_compact_finiteFibers
    R e c hR hDim hFibers

end
end QuaternionicSymmetry.HolomorphicLinePowerSeparationRestrictedEstimate
