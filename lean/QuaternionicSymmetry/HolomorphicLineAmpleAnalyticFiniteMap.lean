import QuaternionicSymmetry.HolomorphicLineAmpleRatioSeparation
import QuaternionicSymmetry.HolomorphicSeparatedFiniteFibersSource
import QuaternionicSymmetry.ComplexProjectiveHausdorff
import QuaternionicSymmetry.HolomorphicFiniteMapDimensionSource
import QuaternionicSymmetry.HolomorphicAnalyticSubsetFiniteSource

/-! An analytic proof of finite fibers for a generated ample holomorphic
line core. It uses Demailly's compact-analytic-subset theorem, with the
required holomorphic separating functions built internally as ratios of
sections of an actual very-ample tensor power. -/

namespace QuaternionicSymmetry.HolomorphicLineAmpleAnalyticFiniteMap

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
open QuaternionicSymmetry.HolomorphicLineCoreAmpleFiniteMap
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open QuaternionicSymmetry.HolomorphicLineSectionRatios
open QuaternionicSymmetry.HolomorphicLineAmpleRatioSeparation
open QuaternionicSymmetry.HolomorphicSeparatedFiniteFibersSource
open QuaternionicSymmetry.HolomorphicFiniteMapDimensionSource
open QuaternionicSymmetry.HolomorphicAnalyticSubsetFiniteSource
open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section
universe uB uF uI

variable {B : Type uB} {F : Type uF}
  [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
  [CompactSpace B] [Nonempty B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
  (L : LineCore.{uI} (B := B) 𝓘(ℂ,F))

omit [Nonempty B] in
/-- Demailly's general theorem, applied to the actual complete linear
system and the actual ratio functions on a single nonzero-section chart. -/
theorem finiteFibers_of_ample_generated
    (hSource : SeparatedCompactProjectiveFiberFiniteTheorem.{uB,uF})
    (hAmple : AmpleCore 𝓘(ℂ,F) L)
    (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ
      (GlobalSections 𝓘(ℂ,F) L))
    (hGen : GloballyGenerated 𝓘(ℂ,F) L)
    (p : Space d) :
    ((projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen) ⁻¹' {p}).Finite := by
  let g := projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen
  obtain ⟨i, hi⟩ := exists_mem_affineDomain d p
  let s := b i
  let U := nonzeroSet 𝓘(ℂ,F) L s
  have hFiberU : g ⁻¹' {p} ⊆ U := by
    intro x hx
    have hxg : g x = p := hx
    have hmem : g x ∈ affineDomain d i := hxg ▸ hi
    change s x ≠ 0
    have hcoord := (mem_affineDomain_mk d i
      (basisEvaluation 𝓘(ℂ,F) L d b x)
      (basisEvaluation_ne_zero 𝓘(ℂ,F) L d b
        (by simp [(globallyGenerated_iff_baseLocus_empty 𝓘(ℂ,F) L).1 hGen]))).1 hmem
    exact hcoord
  have hSet : U ∩ g ⁻¹' {p} = g ⁻¹' {p} := Set.inter_eq_right.mpr hFiberU
  have hCompact : IsCompact (U ∩ g ⁻¹' {p}) := by
    rw [hSet]
    exact ((isClosed_singleton.preimage
      (projectiveEvaluationOfGenerated_contMDiff 𝓘(ℂ,F) L d b hGen).continuous)).isCompact
  obtain ⟨k, _, hVery⟩ := hAmple
  have hSep : ∀ x y : B, x ∈ U → y ∈ U → x ≠ y →
      ∃ f : B → ℂ,
        ContMDiffOn 𝓘(ℂ,F) 𝓘(ℂ,ℂ) ∞ f U ∧ f x ≠ f y := by
    intro x y hx hy hxy
    obtain ⟨t, ht⟩ := ratios_separate_of_veryAmplePower
      𝓘(ℂ,F) L k hVery s x y hx hy hxy
    exact ⟨sectionRatio 𝓘(ℂ,F) L k s t,
      sectionRatio_contMDiffOn 𝓘(ℂ,F) L k s t, ht⟩
  have hF := hSource U (isOpen_nonzeroSet 𝓘(ℂ,F) L s)
    hSep d g (projectiveEvaluationOfGenerated_contMDiff
      𝓘(ℂ,F) L d b hGen).contMDiffOn p hCompact
  rwa [hSet] at hF

/-- The ambient complete-linear-system section count, now using only the
two Demailly analytic source theorems and actual ampleness/generation. -/
theorem ample_generated_section_finrank_bound_analytic
    (hSeparated : SeparatedCompactProjectiveFiberFiniteTheorem.{uB,uF})
    (hDim : FiniteHolomorphicMapDimensionTheorem.{uB,uF})
    (hAmple : AmpleCore 𝓘(ℂ,F) L)
    (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ
      (GlobalSections 𝓘(ℂ,F) L))
    (hGen : GloballyGenerated 𝓘(ℂ,F) L) :
    Module.finrank ℂ F + 1 ≤
      Module.finrank ℂ (GlobalSections 𝓘(ℂ,F) L) := by
  exact section_finrank_bound_of_compact_finiteFibers L d b hGen hDim
    (finiteFibers_of_ample_generated L hSeparated hAmple d b hGen)

/-- The ambient bound stated against Demailly's literal compact-analytic-
subset theorem, with the projective-fiber analyticity derived internally. -/
theorem ample_generated_section_finrank_bound_literal
    (hLiteral : SeparatedCompactAnalyticSubsetFiniteTheorem.{uB,uF})
    (hDim : FiniteHolomorphicMapDimensionTheorem.{uB,uF})
    (hAmple : AmpleCore 𝓘(ℂ,F) L)
    (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ
      (GlobalSections 𝓘(ℂ,F) L))
    (hGen : GloballyGenerated 𝓘(ℂ,F) L) :
    Module.finrank ℂ F + 1 ≤
      Module.finrank ℂ (GlobalSections 𝓘(ℂ,F) L) :=
  ample_generated_section_finrank_bound_analytic L
    (separatedCompactProjectiveFiber_of_analyticSubset hLiteral)
    hDim hAmple d b hGen

end
end QuaternionicSymmetry.HolomorphicLineAmpleAnalyticFiniteMap
