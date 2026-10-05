import QuaternionicSymmetry.HolomorphicLineAmpleAnalyticFiniteMap

/-! The finite-fiber argument only needs actual holomorphic sections of one
power separating points by ratios on the nonzero locus of each section of
the original line. This separates the analytic Demailly step from the
stronger complete-system definition of `AmpleCore`. -/

namespace QuaternionicSymmetry.HolomorphicLinePowerSeparationFiniteFibers
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineTensorPowerClasses HolomorphicLineSectionRatios
open HolomorphicSeparatedFiniteFibersSource
open HolomorphicLineAmpleRatioSeparation
open ComplexProjectiveTopology
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section

variable {B F : Type} [TopologicalSpace B] [T2Space B]
  [SecondCountableTopology B] [CompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
  (L : LineCore.{0} (B := B) 𝓘(ℂ,F))

/-- A concrete geometric separation condition on actual power sections.
It has no finite-map or section-dimension conclusion. -/
def PowerRatioSeparates (k : ℕ) : Prop :=
  ∀ (s : GlobalSections 𝓘(ℂ,F) L) (x y : B),
    x ∈ nonzeroSet 𝓘(ℂ,F) L s →
    y ∈ nonzeroSet 𝓘(ℂ,F) L s → x ≠ y →
    ∃ t : GlobalSections 𝓘(ℂ,F) (powerCoreRep 𝓘(ℂ,F) L k),
      sectionRatio 𝓘(ℂ,F) L k s t x ≠
        sectionRatio 𝓘(ℂ,F) L k s t y

/-- The actual Demailly compact-fiber theorem from the point-separating
power-section condition, with all ratio holomorphicity constructed in Lean. -/
theorem finiteFibers_of_powerRatioSeparates
    (hSource : SeparatedCompactProjectiveFiberFiniteTheorem.{0,0})
    (k : ℕ) (hSep : PowerRatioSeparates L k)
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
  have hAnalyticSep : ∀ x y : B, x ∈ U → y ∈ U → x ≠ y →
      ∃ f : B → ℂ,
        ContMDiffOn 𝓘(ℂ,F) 𝓘(ℂ,ℂ) ∞ f U ∧ f x ≠ f y := by
    intro x y hx hy hxy
    obtain ⟨t, ht⟩ := hSep s x y hx hy hxy
    exact ⟨sectionRatio 𝓘(ℂ,F) L k s t,
      sectionRatio_contMDiffOn 𝓘(ℂ,F) L k s t, ht⟩
  have hF := hSource U (isOpen_nonzeroSet 𝓘(ℂ,F) L s)
    hAnalyticSep d g (projectiveEvaluationOfGenerated_contMDiff
      𝓘(ℂ,F) L d b hGen).contMDiffOn p hCompact
  rwa [hSet] at hF

end
end QuaternionicSymmetry.HolomorphicLinePowerSeparationFiniteFibers
