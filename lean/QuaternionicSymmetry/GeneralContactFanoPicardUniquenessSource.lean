import QuaternionicSymmetry.GeneralContactFanoPicardHomogeneitySource
import QuaternionicSymmetry.GeneralHolomorphicDistributionUniqueFull

/-!
# Reviewed general contact-distribution uniqueness consequence

**Reviewed derived general-source companion T2-U to T2-A.** BKK Proposition 2.3
(printed p. 1864) makes the contact distribution unique on both the
Picard-generator and projectivized-cotangent alternatives. The remaining
projective-space alternative has contact quotient line `O(2)`, whose integral
powers do not generate its Picard group. Therefore, if the *actual* contact
line generates Picard, the distribution is unique. A biholomorphism pulls a
complex contact distribution back to another contact distribution; uniqueness
then makes every actual biholomorphism preserve the original distribution.

The analytic formulation also uses the same general Chow/GAGA algebraization
and contact-line matching chain disclosed for T2-A. Nothing in this file
proves that literature chain internally, asserts uniqueness on a particular twistor, or
turns projective-space contact-structure equivalence into point transitivity.
-/

namespace QuaternionicSymmetry.GeneralContactFanoPicardUniquenessSource

open GeneralContactFanoPicardHomogeneitySource
open GeneralComplexContactData
open ManifoldTwistorLeBrunComplexAtlas
open GeneralHolomorphicDistributionUniqueFull
open HolomorphicLineCoreClasses HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff

noncomputable section

/-- Universal derived BKK uniqueness implication, conditional on the same
genuine complex-contact and ampleness hypotheses as T2-A. It demands an
actual contact-line power-map bijection before asserting preservation by
every biholomorphism of the same complex manifold. -/
def AnalyticContactPicardGeneratorPreservesDistribution : Prop :=
  ∀ {R H Z : Type}
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
    (IR : ModelWithCorners ℝ R H) [IsManifold IR ∞ Z]
    [CompactSpace Z] [T2Space Z] [SecondCountableTopology Z]
    [ConnectedSpace Z]
    (n : ℕ) (_hn : 1 ≤ n)
    (G : ContactGeometry (IR := IR) (Z := Z) n)
    (D : Z → Submodule ℂ (ComplexTwistorModel n)),
    ContactGeometry.IsComplexContactKernel IR G D →
    letI := G.charts
    letI := G.complexManifold
    AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (ContactGeometry.lineCore IR G) →
    Function.Bijective (fun r : ℤ =>
      (Quotient.mk _ (ContactGeometry.lineCore IR G) :
        CoreClass.{0} (B := Z) 𝓘(ℂ,ComplexTwistorModel n)) ^ r) →
    AllAutomorphismsPreserve D

end
end QuaternionicSymmetry.GeneralContactFanoPicardUniquenessSource
