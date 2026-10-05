import QuaternionicSymmetry.HolomorphicLineSectionRatios
import QuaternionicSymmetry.HolomorphicLineCoreAmpleness

/-! A very-ample power supplies actual holomorphic scalar functions that
separate points on the nonzero locus of any section of the underlying line. -/

namespace QuaternionicSymmetry.HolomorphicLineAmpleRatioSeparation

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
open QuaternionicSymmetry.HolomorphicLineCoreAmpleFiniteMap
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open QuaternionicSymmetry.HolomorphicLineSectionRatios
open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H) [IsManifold IB ∞ B]
  (L : LineCore.{u} (B := B) IB)

omit [IsManifold IB ∞ B] in
theorem ratios_separate_of_veryAmplePower
    (k : ℕ) (hVery : VeryAmpleCore IB (powerCoreRep IB L k))
    (s : GlobalSections IB L) (x y : B)
    (hx : x ∈ nonzeroSet IB L s) (hy : y ∈ nonzeroSet IB L s)
    (hxy : x ≠ y) :
    ∃ t : GlobalSections IB (powerCoreRep IB L k),
      sectionRatio IB L k s t x ≠ sectionRatio IB L k s t y := by
  obtain ⟨d, b, hGen, hEmbed, _⟩ := hVery
  let P := powerCoreRep IB L k
  let px := projectiveEvaluationOfGenerated IB P d b hGen x
  let py := projectiveEvaluationOfGenerated IB P d b hGen y
  have hp : px ≠ py := fun heq => hxy (hEmbed.injective heq)
  by_contra h
  have hrat (i : Fin (d + 1)) :
      sectionRatio IB L k s (b i) x = sectionRatio IB L k s (b i) y := by
    by_contra hi
    exact h ⟨b i, hi⟩
  have hsx : (show ℂ from s x) ^ k ≠ 0 := pow_ne_zero k hx
  have hsy : (show ℂ from s y) ^ k ≠ 0 := pow_ne_zero k hy
  have hcoord (i : Fin (d + 1)) :
      (show ℂ from b i x) = ((show ℂ from s x) ^ k /
        (show ℂ from s y) ^ k) * (show ℂ from b i y) := by
    have hi := hrat i
    change (show ℂ from b i x) / ((show ℂ from s x) ^ k) =
      (show ℂ from b i y) / ((show ℂ from s y) ^ k) at hi
    have hcross : (show ℂ from b i x) * ((show ℂ from s y) ^ k) =
        ((show ℂ from s x) ^ k) * (show ℂ from b i y) :=
      ((div_eq_div_iff hsx hsy).1 hi).trans (mul_comm _ _)
    calc
      (show ℂ from b i x) =
          (((show ℂ from s x) ^ k) * (show ℂ from b i y)) /
            ((show ℂ from s y) ^ k) := (eq_div_iff hsy).2 hcross
      _ = ((show ℂ from s x) ^ k / (show ℂ from s y) ^ k) *
          (show ℂ from b i y) := by ring
  have hv : basisEvaluation IB P d b x =
      ((show ℂ from s x) ^ k / (show ℂ from s y) ^ k) •
        basisEvaluation IB P d b y := by
    funext i
    exact hcoord i
  apply hp
  change Projectivization.mk ℂ (basisEvaluation IB P d b x) _ =
    Projectivization.mk ℂ (basisEvaluation IB P d b y) _
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  exact ⟨((show ℂ from s x) ^ k / (show ℂ from s y) ^ k), hv.symm⟩

end
end QuaternionicSymmetry.HolomorphicLineAmpleRatioSeparation
