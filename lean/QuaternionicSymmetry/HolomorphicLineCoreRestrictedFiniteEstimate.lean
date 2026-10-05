import QuaternionicSymmetry.HolomorphicLineCoreCompleteRestriction
import QuaternionicSymmetry.HolomorphicLineAmpleAnalyticFiniteMap
import QuaternionicSymmetry.HolomorphicFiniteMapDimensionSource

/-! A checked restricted-section estimate from genuine complex geometry:
an ample, globally generated ambient line has finite complete-system
fibers by Demailly's analytic compact-fiber theorem after actual
holomorphic section ratios have been constructed. These finite fibers pass
internally to the complete system on an injectively included complex
submanifold; Demailly's finite-map dimension theorem then yields the
number of restricted sections. No desired numerical bound is a premise. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreRestrictedFiniteEstimate

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
open QuaternionicSymmetry.HolomorphicLineCoreCompleteRestriction
open QuaternionicSymmetry.HolomorphicLineCoreAmpleFiniteMap
open QuaternionicSymmetry.HolomorphicFiniteMapDimensionSource
open QuaternionicSymmetry.HolomorphicSeparatedFiniteFibersSource
open QuaternionicSymmetry.HolomorphicLineAmpleAnalyticFiniteMap
open QuaternionicSymmetry.HolomorphicAnalyticSubsetFiniteSource
open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff
noncomputable section
universe uB uF uB' uF' uI

variable {B : Type uB} {F : Type uF}
  {B' : Type uB'} {F' : Type uF'}
  [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
  [CompactSpace B] [Nonempty B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F B]
  [TopologicalSpace B'] [T2Space B'] [SecondCountableTopology B']
  [CompactSpace B'] [Nonempty B']
  [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  [ChartedSpace F' B']
  [IsManifold 𝓘(ℂ,F) ∞ B] [IsManifold 𝓘(ℂ,F') ∞ B']
  (L : LineCore.{uI} (B := B) 𝓘(ℂ,F))
  (f : B' → B) (hf : ContMDiff 𝓘(ℂ,F') 𝓘(ℂ,F) ∞ f)
  (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections 𝓘(ℂ,F) L))
  (hGen : GloballyGenerated 𝓘(ℂ,F) L)
  (e : ℕ) (c : Module.Basis (Fin (e + 1)) ℂ
    (GlobalSections 𝓘(ℂ,F') (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf)))

include d b hGen e c

omit [Nonempty B] in
/-- The source-faithful analytic route: Demailly II §5.1 supplies only the
general compact-analytic-fiber finiteness principle, while II §8.1 supplies
the finite-holomorphic-map dimension inequality. All ampleness, generation,
restriction, and projective evaluation are actual constructed geometry. -/
theorem restricted_section_finrank_bound_analytic
    (hSeparated : SeparatedCompactProjectiveFiberFiniteTheorem.{uB,uF})
    (hDim : FiniteHolomorphicMapDimensionTheorem.{uB',uF'})
    (hAmple : AmpleCore 𝓘(ℂ,F) L)
    (hfInj : Function.Injective f) :
    Module.finrank ℂ F' + 1 ≤
      Module.finrank ℂ
        (GlobalSections 𝓘(ℂ,F') (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf)) := by
  let R := pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf
  let hR : GloballyGenerated 𝓘(ℂ,F') R :=
    globallyGenerated_pullback 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf hGen
  have hAmbient : ∀ p : Space d,
      ((projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen) ⁻¹' {p}).Finite :=
    finiteFibers_of_ample_generated L hSeparated hAmple d b hGen
  have hFibers : ∀ q : Space e,
      ((projectiveEvaluationOfGenerated 𝓘(ℂ,F') R e c hR) ⁻¹' {q}).Finite := by
    intro q
    exact completeRestrictedMap_finiteFibers_of_ambient
      𝓘(ℂ,F) 𝓘(ℂ,F') L f hf d b hGen e c hfInj hAmbient q
  exact section_finrank_bound_of_compact_finiteFibers
    R e c hR hDim hFibers

omit [Nonempty B] in
/-- The restricted estimate against the literal Demailly II §5.1 theorem
for compact analytic subsets and II §8.1 finite-map dimensions. The
projective-fiber local equations, section ratios, and restriction step are
all proved inside Lean. -/
theorem restricted_section_finrank_bound_literal
    (hLiteral : SeparatedCompactAnalyticSubsetFiniteTheorem.{uB,uF})
    (hDim : FiniteHolomorphicMapDimensionTheorem.{uB',uF'})
    (hAmple : AmpleCore 𝓘(ℂ,F) L)
    (hfInj : Function.Injective f) :
    Module.finrank ℂ F' + 1 ≤
      Module.finrank ℂ
        (GlobalSections 𝓘(ℂ,F') (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf)) :=
  restricted_section_finrank_bound_analytic L f hf d b hGen e c
    (separatedCompactProjectiveFiber_of_analyticSubset hLiteral)
    hDim hAmple hfInj

end
end QuaternionicSymmetry.HolomorphicLineCoreRestrictedFiniteEstimate
