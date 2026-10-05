import QuaternionicSymmetry.HolomorphicFiniteMapDimensionSource
import QuaternionicSymmetry.HolomorphicLineCoreAmpleness

/-! A source-faithful interface for the general ample-and-generated section
estimate. `AmpleCore` is defined by an actual positive line-core power with
a complete holomorphic projective embedding and injective manifold
derivative. The finite-fiber theorem is Lazarsfeld, *Positivity in Algebraic
Geometry I*, Chapter 1, Corollary 1.2.15, printed p.28; using it here for
compact complex manifolds also invokes Kodaira/Chow/GAGA to pass from this
analytic embedding to the algebraic complete-linear-system statement.

No line's ampleness, finite fibers, or dimension inequality is posited as a
field on a particular twistor. The universal general-theorem premise is
separate from Demailly's analytic finite-map dimension theorem. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreAmpleFiniteMap

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open QuaternionicSymmetry.HolomorphicFiniteMapDimensionSource
open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff
noncomputable section
universe uB uH uF uI

variable {B : Type uB} {H : Type uH} {F : Type uF}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace H B] (IB : ModelWithCorners ℂ F H)
  [IsManifold IB ∞ B]
  (L : LineCore.{uI} (B := B) IB)

/-- Author-hosted Lazarsfeld Corollary 1.2.15, with Kodaira/Chow/GAGA for
the analytic presentation: a globally generated ample line's actual
complete-system map has finite fibers. `AmpleCore` carries the explicit
positive-power embedding data, not an opaque Fano flag. -/
def AmpleGeneratedFiniteFibersTheorem : Prop :=
  ∀ {B : Type uB} {F : Type uF}
    [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
    [CompactSpace B] [Nonempty B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
    (L : LineCore.{uI} (B := B) 𝓘(ℂ,F)),
    AmpleCore 𝓘(ℂ,F) L →
    ∀ (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections 𝓘(ℂ,F) L))
      (hGen : GloballyGenerated 𝓘(ℂ,F) L) (p : Space d),
      ((projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen) ⁻¹' {p}).Finite

/-- The draft's general ample-plus-generated section lower bound on an
actual represented holomorphic line, proved by composing the two precise
general literature premises with our actual complete evaluation map.
There is no assumption on the desired numerical bound. -/
theorem ample_generated_section_finrank_bound
    {B : Type uB} {F : Type uF}
    [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
    [CompactSpace B] [Nonempty B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
    (hFinite : AmpleGeneratedFiniteFibersTheorem.{uB,uF,uI})
    (hDim : FiniteHolomorphicMapDimensionTheorem.{uB,uF})
    (L : LineCore.{uI} (B := B) 𝓘(ℂ,F))
    (hAmple : AmpleCore 𝓘(ℂ,F) L)
    (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections 𝓘(ℂ,F) L))
    (hGen : GloballyGenerated 𝓘(ℂ,F) L) [T2Space (Space d)] :
    Module.finrank ℂ F + 1 ≤ Module.finrank ℂ (GlobalSections 𝓘(ℂ,F) L) := by
  exact section_finrank_bound_of_compact_finiteFibers L d b hGen hDim
    (hFinite L hAmple d b hGen)

end
end QuaternionicSymmetry.HolomorphicLineCoreAmpleFiniteMap
