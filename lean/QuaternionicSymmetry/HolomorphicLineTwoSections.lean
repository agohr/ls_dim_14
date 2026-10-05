import QuaternionicSymmetry.HolomorphicLinePowerSeparationRestrictedEstimate
import Mathlib.Geometry.Manifold.Complex

/-! A connected compact submanifold with two distinct points needs at least
two sections of a generated line whose power-section ratios separate points.
This weaker estimate suffices for extremal isolation and avoids analytic
subsets and finite holomorphic maps entirely. -/
namespace QuaternionicSymmetry.HolomorphicLineTwoSections
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineSectionRatios HolomorphicLineTensorPowerClasses
open HolomorphicLinePowerSeparationFiniteFibers HolomorphicLineFiniteSectionsSource
open scoped Manifold ContDiff
noncomputable section

variable {B Y F H : Type}
  [TopologicalSpace B] [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
  [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [CompactSpace Y] [PreconnectedSpace Y] [Nontrivial Y]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  [ChartedSpace H Y] [IsManifold 𝓘(ℂ,H) ∞ Y]

theorem restricted_sections_ge_two
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (L : LineCore.{0} (B := B) 𝓘(ℂ,F))
    (f : Y → B) (hf : ContMDiff 𝓘(ℂ,H) 𝓘(ℂ,F) ∞ f)
    (hGen : GloballyGenerated 𝓘(ℂ,F) L)
    (k : ℕ) (hSep : PowerRatioSeparates L k)
    (hfInj : Function.Injective f) :
    2 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,H) (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,H) L f hf)) := by
  classical
  let R := pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,H) L f hf
  let S := GlobalSections 𝓘(ℂ,H) R
  letI : FiniteDimensional ℂ S := hFinite R
  let ρ := restrictionLinear 𝓘(ℂ,F) 𝓘(ℂ,H) L f hf
  obtain ⟨x,y,hxy⟩ := exists_pair_ne Y
  obtain ⟨s,hs⟩ := hGen (f x)
  have hsR : ρ s ≠ 0 := by
    intro heq
    exact hs (congrArg (fun u : S => u x) heq)
  by_contra hsmall
  have hdim : Module.finrank ℂ S = 1 := by
    have hp : 0 < Module.finrank ℂ S := Module.finrank_pos_iff.mpr
      (not_subsingleton_iff_nontrivial.mp (fun h => hsR (h.elim _ _)))
    change ¬ 2 ≤ Module.finrank ℂ S at hsmall
    omega
  have hspan := (finrank_eq_one_iff_of_nonzero' (ρ s) hsR).mp hdim
  have hnonzero (z : Y) : s (f z) ≠ 0 := by
    intro hsz
    obtain ⟨t,ht⟩ := hGen (f z)
    obtain ⟨a,ha⟩ := hspan (ρ t)
    have heq := congrArg (fun u : S => u z) ha
    change a • s (f z) = t (f z) at heq
    rw [hsz,smul_zero] at heq
    exact ht heq.symm
  obtain ⟨t,ht⟩ := hSep s (f x) (f y) (hnonzero x) (hnonzero y)
    (fun h => hxy (hfInj h))
  have hhol : ContMDiff 𝓘(ℂ,H) 𝓘(ℂ,ℂ) ∞
      (fun z => sectionRatio 𝓘(ℂ,F) L k s t (f z)) := by
    apply contMDiffOn_univ.mp
    exact (sectionRatio_contMDiffOn 𝓘(ℂ,F) L k s t).comp hf.contMDiffOn
      (fun z _ => hnonzero z)
  exact ht ((hhol.mdifferentiable (by simp)).apply_eq_of_compactSpace x y)

theorem restricted_sections_ge_two_of_ample
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (L : LineCore.{0} (B := B) 𝓘(ℂ,F))
    (f : Y → B) (hf : ContMDiff 𝓘(ℂ,H) 𝓘(ℂ,F) ∞ f)
    (hGen : GloballyGenerated 𝓘(ℂ,F) L)
    (hAmple : HolomorphicLineCoreAmpleFiniteMap.AmpleCore 𝓘(ℂ,F) L)
    (hfInj : Function.Injective f) :
    2 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,H) (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,H) L f hf)) := by
  obtain ⟨k,hk,hVery⟩ := hAmple
  exact restricted_sections_ge_two hFinite L f hf hGen k
    (HolomorphicLineAmpleRatioSeparation.ratios_separate_of_veryAmplePower
      𝓘(ℂ,F) L k hVery) hfInj

end
end QuaternionicSymmetry.HolomorphicLineTwoSections
