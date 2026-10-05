import QuaternionicSymmetry.GeneralComplexContactData
import QuaternionicSymmetry.HolomorphicLineCoreAmpleness
import QuaternionicSymmetry.HolomorphicLineCoreClasses
import QuaternionicSymmetry.HolomorphicLineCoreClassGroup
import QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
import QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphisms

/-!
# Derived analytic contact-Fano Picard-or-homogeneity input

**Reviewed derived literature input T2-A, not a Lean proof of BKK.** A positive
complete-linear-system embedding (the actual meaning of `AmpleCore`) leads by
Chow/GAGA to a smooth projective contact variety. The general contact
canonical-power formula makes it Fano. BKK, *Special lines on contact
manifolds*, Ann. Inst. Fourier 72 (2022), Proposition 2.3, p. 1864, then
gives either `Pic = ℤ[L]`, the cotangent projective flag, or projective space.
The latter two have transitive *contact* automorphism groups: use the
canonical flag contact action and BKK uniqueness in the flag case; use a
standard symplectic projective contact action and LeBrun, *Fano Manifolds,
Contact Structures, and Quaternionic Geometry*, Proposition 2.3, to compare
the given contact form in the projective-space case. Analytic Picard classes
and the actual contact distribution must be matched under Chow/GAGA.

None of those literature steps is proved in this file. The corollary is a
single explicitly passed proposition, type/source-reviewed on 28 September
2026. The registry and STAGE2_BKK_ANALYTIC_COROLLARY_20260928.md disclose its
Serre/Atiyah-Macdonald/BKK/LeBrun derivation, including smoothness, full
Picard comparison, and contact-form/Levi transport under algebraization.
It is universal over compact complex contact manifolds, has no quaternionic
or dimension-14 classification conclusion, and does not assume transitivity
or Picard generation as a field of the contact input.
-/

namespace QuaternionicSymmetry.GeneralContactFanoPicardHomogeneitySource

open GeneralComplexContactData
open ManifoldTwistorLeBrunComplexAtlas
open HolomorphicLineCoreClasses HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineTensorPowerClasses
open GeneralHolomorphicDistributionAutomorphisms
open scoped Manifold ContDiff

noncomputable section

/-- The actual represented holomorphic contact quotient line of general
complex-contact geometry, using its own bundle atlas and holomorphicity. -/
def ContactGeometry.lineCore
    {R H Z : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
    (IR : ModelWithCorners ℝ R H) [IsManifold IR ∞ Z]
    {n : ℕ} (G : ContactGeometry (IR := IR) (Z := Z) n) :
    letI := G.charts
    LineCore.{0} (B := Z) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := G.charts
  exact ⟨G.Index, G.line, G.lineHolomorphic⟩

/-- A complex distribution is literally the kernel of the contact quotient
form after the actual complex-to-real tangent-chart comparison. This is an
equality of sets on every genuine tangent fiber, not an exception marker. -/
def ContactGeometry.IsComplexContactKernel
    {R H Z : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
    (IR : ModelWithCorners ℝ R H) [IsManifold IR ∞ Z]
    {n : ℕ} (G : ContactGeometry (IR := IR) (Z := Z) n)
    (D : Z → Submodule ℂ (ComplexTwistorModel n)) : Prop :=
  letI := G.charts
  letI := G.realManifold
  ∀ z v, v ∈ D z ↔
    G.theta z
      (mfderiv 𝓘(ℝ,ComplexTwistorModel n) IR (id : Z → Z) z v) = 0

/-- **Reviewed derived literature corollary T2-A.** Its first conclusion is a
bijective power map on the actual represented holomorphic line-class group;
its second is transitivity of actual biholomorphisms preserving the same
complex contact kernel in both directions. Chow/GAGA/Picard and exceptional
contact actions are part of the disclosed external derivation, not internally
proved here. Algebraic group/action comparison is not a conclusion. -/
def AnalyticContactPicardOrHomogeneousCorollary : Prop :=
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
        CoreClass.{0} (B := Z) 𝓘(ℂ,ComplexTwistorModel n)) ^ r) ∨
    (∀ z w : Z, ∃ f : Automorphisms D, f.1 z = w)

end
end QuaternionicSymmetry.GeneralContactFanoPicardHomogeneitySource
