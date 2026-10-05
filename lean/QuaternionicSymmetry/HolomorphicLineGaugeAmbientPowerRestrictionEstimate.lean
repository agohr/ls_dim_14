import QuaternionicSymmetry.HolomorphicLinePowerSeparationRestrictedEstimate
import QuaternionicSymmetry.HolomorphicLinePullbackPowerRatioSeparation
import QuaternionicSymmetry.HolomorphicLineGaugePowerRatioSeparation

/-! An ambient very-ample power, an injective holomorphic inclusion, and
an actual gauge to the intrinsic generated line suffice for the intrinsic
restricted-section dimension bound. No ampleness premise on that intrinsic
line is needed. -/

namespace QuaternionicSymmetry.HolomorphicLineGaugeAmbientPowerRestrictionEstimate
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineTensorPowerClasses
open HolomorphicLineGauge
open HolomorphicLinePowerSeparationRestrictedEstimate
open HolomorphicLinePullbackPowerRatioSeparation
open HolomorphicLineGaugePowerRatioSeparation
open HolomorphicLineFiniteSectionsSource
open HolomorphicAnalyticSubsetFiniteSource
open HolomorphicFiniteMapDimensionSource
open scoped Manifold ContDiff
noncomputable section

variable {B N Y F G H : Type}
  [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
  [CompactSpace B] [Nonempty B]
  [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
  [CompactSpace N] [Nonempty N]
  [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [CompactSpace Y] [Nonempty Y]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
  [ChartedSpace G N] [IsManifold 𝓘(ℂ,G) ∞ N]
  [ChartedSpace H Y] [IsManifold 𝓘(ℂ,H) ∞ Y]

theorem intrinsic_restricted_bound_of_ambient_veryAmplePower
    (LB : LineCore.{0} (B := B) 𝓘(ℂ,F))
    (LN : LineCore.{0} (B := N) 𝓘(ℂ,G))
    (f : N → B) (hf : ContMDiff 𝓘(ℂ,G) 𝓘(ℂ,F) ∞ f)
    (hfInj : Function.Injective f)
    (e : letI := LN.holomorphic
      letI := (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,G) LB f hf).holomorphic
      GaugeIso (IB := 𝓘(ℂ,G)) LN.core
        (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,G) LB f hf).core)
    (j : Y → N) (hj : ContMDiff 𝓘(ℂ,H) 𝓘(ℂ,G) ∞ j)
    (hjInj : Function.Injective j)
    (hGen : GloballyGenerated 𝓘(ℂ,G) LN)
    (k : ℕ) (hVery : VeryAmpleCore 𝓘(ℂ,F)
      (powerCoreRep 𝓘(ℂ,F) LB k))
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (hLiteral : SeparatedCompactAnalyticSubsetFiniteTheorem.{0,0})
    (hDim : FiniteHolomorphicMapDimensionTheorem.{0,0}) :
    Module.finrank ℂ H + 1 ≤ Module.finrank ℂ
      (GlobalSections 𝓘(ℂ,H)
        (pullbackLineCore 𝓘(ℂ,G) 𝓘(ℂ,H) LN j hj)) := by
  let Lpull := pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,G) LB f hf
  letI := LN.holomorphic
  letI := Lpull.holomorphic
  have hPull := pullback_powerRatioSeparates_of_ambient_veryAmple
    LB f hf hfInj k hVery
  have hSep := powerRatioSeparates_of_gauge LN Lpull e k hPull
  exact restricted_section_finrank_bound_of_powerRatioSeparates
    hFinite LN j hj hGen k hSep hLiteral hDim hjInj

end
end QuaternionicSymmetry.HolomorphicLineGaugeAmbientPowerRestrictionEstimate
