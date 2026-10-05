import QuaternionicSymmetry.HolomorphicLineRestrictedPowerSections
import QuaternionicSymmetry.HolomorphicLinePowerSeparationFiniteFibers
import QuaternionicSymmetry.HolomorphicLineCoreAmpleness

/-! Restricting an actual ambient very-ample power supplies the precise
ratio-separating power sections needed on an injectively embedded source,
even when a section of the first-power restricted line does not extend. -/

namespace QuaternionicSymmetry.HolomorphicLinePullbackPowerRatioSeparation
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineTensorPowerClasses HolomorphicLineSectionRatios
open HolomorphicLineRestrictedPowerSections
open HolomorphicLinePowerSeparationFiniteFibers
open ComplexProjectiveTopology
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section

variable {B B' F F' : Type}
  [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [ChartedSpace F B] [ChartedSpace F' B']
  [IsManifold 𝓘(ℂ,F) ∞ B] [IsManifold 𝓘(ℂ,F') ∞ B']
  (L : LineCore.{0} (B := B) 𝓘(ℂ,F))
  (f : B' → B) (hf : ContMDiff 𝓘(ℂ,F') 𝓘(ℂ,F) ∞ f)

theorem pullback_powerRatioSeparates_of_ambient_veryAmple
    (hfInj : Function.Injective f)
    (k : ℕ) (hVery : VeryAmpleCore 𝓘(ℂ,F)
      (powerCoreRep 𝓘(ℂ,F) L k)) :
    PowerRatioSeparates
      (pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf) k := by
  obtain ⟨d,b,hGen,hEmbed,_⟩ := hVery
  let R := pullbackLineCore 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf
  let P := powerCoreRep 𝓘(ℂ,F) L k
  intro s x y hx hy hxy
  have hfxfy : f x ≠ f y := fun h => hxy (hfInj h)
  let px := projectiveEvaluationOfGenerated 𝓘(ℂ,F) P d b hGen (f x)
  let py := projectiveEvaluationOfGenerated 𝓘(ℂ,F) P d b hGen (f y)
  have hp : px ≠ py := fun heq => hfxfy (hEmbed.injective heq)
  by_contra h
  have hrat (i : Fin (d + 1)) :
      sectionRatio 𝓘(ℂ,F') R k s
        (restrictedPowerSection 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf k (b i)) x =
      sectionRatio 𝓘(ℂ,F') R k s
        (restrictedPowerSection 𝓘(ℂ,F) 𝓘(ℂ,F') L f hf k (b i)) y := by
    by_contra hi
    exact h ⟨_, hi⟩
  have hsx : (show ℂ from s x) ^ k ≠ 0 := pow_ne_zero k hx
  have hsy : (show ℂ from s y) ^ k ≠ 0 := pow_ne_zero k hy
  have hcoord (i : Fin (d + 1)) :
      (show ℂ from b i (f x)) =
        ((show ℂ from s x) ^ k / (show ℂ from s y) ^ k) *
          (show ℂ from b i (f y)) := by
    have hi := hrat i
    change (show ℂ from b i (f x)) / ((show ℂ from s x) ^ k) =
      (show ℂ from b i (f y)) / ((show ℂ from s y) ^ k) at hi
    have hcross : (show ℂ from b i (f x)) * ((show ℂ from s y) ^ k) =
        ((show ℂ from s x) ^ k) * (show ℂ from b i (f y)) :=
      ((div_eq_div_iff hsx hsy).1 hi).trans (mul_comm _ _)
    calc
      (show ℂ from b i (f x)) =
          (((show ℂ from s x) ^ k) * (show ℂ from b i (f y))) /
            ((show ℂ from s y) ^ k) := (eq_div_iff hsy).2 hcross
      _ = ((show ℂ from s x) ^ k / (show ℂ from s y) ^ k) *
          (show ℂ from b i (f y)) := by ring
  have hv : basisEvaluation 𝓘(ℂ,F) P d b (f x) =
      ((show ℂ from s x) ^ k / (show ℂ from s y) ^ k) •
        basisEvaluation 𝓘(ℂ,F) P d b (f y) := by
    funext i
    exact hcoord i
  apply hp
  change Projectivization.mk ℂ (basisEvaluation 𝓘(ℂ,F) P d b (f x)) _ =
    Projectivization.mk ℂ (basisEvaluation 𝓘(ℂ,F) P d b (f y)) _
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  exact ⟨((show ℂ from s x) ^ k / (show ℂ from s y) ^ k), hv.symm⟩

end
end QuaternionicSymmetry.HolomorphicLinePullbackPowerRatioSeparation
