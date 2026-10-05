import QuaternionicSymmetry.HolomorphicLineCoreProjectiveHolomorphic
import QuaternionicSymmetry.ComplexProjectiveHausdorff
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! A general dimension corollary of the published rank theorem: Lee,
*Introduction to Smooth Manifolds*, 2nd ed., Theorem 4.12, pp.81–82.
Choose a point of maximum derivative rank. Rank is constant nearby, so the
rank normal form and finite fibers force the source dimension to be at most
the target dimension. Realification doubles both complex dimensions.
Properness is retained in the interface but is unnecessary for this argument.
This replaces the older unpublished Demailly locator without changing the
predicate. The general corollary remains an explicit literature premise. -/

namespace QuaternionicSymmetry.HolomorphicFiniteMapDimensionSource

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff
noncomputable section

universe uB uH uF uI

/-- The finite-map dimension corollary, registered universally for actual
holomorphic maps and their literal finite inverse-image sets. -/
def FiniteHolomorphicMapDimensionTheorem : Prop :=
  ∀ {B : Type uB} {F : Type uF}
    [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
    [Nonempty B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
    (d : ℕ) (g : B → Space d),
    ContMDiff 𝓘(ℂ,F) 𝓘(ℂ, Fin d → ℂ) ∞ g →
    IsProperMap g →
    (∀ p : Space d, (g ⁻¹' {p}).Finite) →
    Module.finrank ℂ F ≤ d

variable {B : Type uB} {F : Type uF}
  [TopologicalSpace B] [T2Space B]
  [SecondCountableTopology B] [Nonempty B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
  (L : LineCore.{uI} (B := B) 𝓘(ℂ,F))
  (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections 𝓘(ℂ,F) L))
  (hGen : GloballyGenerated 𝓘(ℂ,F) L)

/-- The standard section count follows from the general finite-map theorem
*only after* properness and finite fibers of this actual complete linear
system have been established. No prescribed Hilbert value is assumed. -/
theorem section_finrank_bound_of_finite_projective_evaluation
    (hDim : FiniteHolomorphicMapDimensionTheorem.{uB,uF})
    (hProper : IsProperMap (projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen))
    (hFibers : ∀ p : Space d,
      ((projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen) ⁻¹' {p}).Finite) :
    Module.finrank ℂ F + 1 ≤ Module.finrank ℂ (GlobalSections 𝓘(ℂ,F) L) := by
  have hd : Module.finrank ℂ F ≤ d :=
    hDim d (projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen)
      (projectiveEvaluationOfGenerated_contMDiff 𝓘(ℂ,F) L d b hGen)
      hProper hFibers
  have hs : Module.finrank ℂ (GlobalSections 𝓘(ℂ,F) L) = d + 1 := by
    simpa using Module.finrank_eq_card_basis b
  omega

/-- For a compact source, the genuine holomorphic complete-linear-system
map is proper once the target's Hausdorff topology is available; then only
finite fibers remain as the independent geometric obligation. -/
theorem section_finrank_bound_of_compact_finiteFibers
    [CompactSpace B]
    (hDim : FiniteHolomorphicMapDimensionTheorem.{uB,uF})
    (hFibers : ∀ p : Space d,
      ((projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen) ⁻¹' {p}).Finite) :
    Module.finrank ℂ F + 1 ≤ Module.finrank ℂ (GlobalSections 𝓘(ℂ,F) L) := by
  have hProper : IsProperMap (projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen) :=
    (projectiveEvaluationOfGenerated_contMDiff 𝓘(ℂ,F) L d b hGen).continuous.isProperMap
  exact section_finrank_bound_of_finite_projective_evaluation
    L d b hGen hDim hProper hFibers

end
end QuaternionicSymmetry.HolomorphicFiniteMapDimensionSource
