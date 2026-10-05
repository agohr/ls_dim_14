import QuaternionicSymmetry.GeneralContactFanoORSWSource
import Mathlib.Analysis.Convex.Extreme
import QuaternionicSymmetry.ManifoldQuaternionicTorusAction

/-!
# Literal analytic maximal-torus recognition interface for ORSW 5.1

Reviewed derived universal corollary of ORSW, Selecta Mathematica 27 (2021),
article 10, Theorem 5.1, publisher-layout p.18. The exact external derivation
and source/type review are recorded in Textbooks/STAGE2_SOURCE_REVIEW_20261001.md;
final global fidelity audit remains separate. As for the rank theorem,
Chow/GAGA, algebraic contact-group comparison and compact-real-form
comparison belong to its disclosed external derivation. Maximality is
actual inclusion maximality of a compact torus in the compact real form.
The canonical contact lift is pinned down by the derivative/contact-form
identity; its fixed-point characters define the actual weight polytope.
The isolated-extrema hypothesis is subsingletonness of the literal connected
fixed component, not a classification marker or section-generation premise.
-/
namespace QuaternionicSymmetry.GeneralContactFanoORSWRecognitionSource

open GeneralContactFanoORSWSource GeneralComplexContactData
open GeneralContactFanoPicardHomogeneitySource ManifoldTwistorLeBrunComplexAtlas
open GeneralHolomorphicDistributionAutomorphisms
open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicLineCoreAmpleFiniteMap CompactLieTorusInputs
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section

variable {R H Z : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  (IR : ModelWithCorners ℝ R H) [IsManifold IR ∞ Z]
  {n : ℕ} (G : ContactGeometry (IR := IR) (Z := Z) n) {r : ℕ}
  (a : Torus r →* Equiv.Perm Z)

/-- The actual quotient derivative lift. The equation fixes its character
normalization and rules out an arbitrary common character twist. -/
def IsCanonicalContactLift
    (Φ : ∀ t z, G.line.Fiber z ≃ₗ[ℂ] G.line.Fiber (a t z)) : Prop :=
  ∀ t z v, Φ t z (G.theta z v) =
    G.theta (a t z) (mfderiv IR IR (a t : Z → Z) z v)

/-- Surjectivity of the genuine quotient form makes the derivative lift
unique, so a separate character twist cannot satisfy its canonical law. -/
theorem canonicalContactLift_unique
    (Φ Ψ : ∀ t z, G.line.Fiber z ≃ₗ[ℂ] G.line.Fiber (a t z))
    (hΦ : IsCanonicalContactLift IR G a Φ)
    (hΨ : IsCanonicalContactLift IR G a Ψ) : Φ = Ψ := by
  funext t z
  apply LinearEquiv.ext
  intro w
  obtain ⟨v,rfl⟩ := G.thetaSurjective z w
  exact (hΦ t z v).trans (hΨ t z v).symm

/-- Fixed fiber characters of the genuine unpowered quotient line. Total
space equality avoids choosing a gauge or a dependent-fiber transport. -/
def FixedFiberCharacter
    (Φ : ∀ t z, G.line.Fiber z ≃ₗ[ℂ] G.line.Fiber (a t z))
    (z : Z) (μ : Fin r → ℤ) : Prop :=
  ∀ t v, (⟨a t z,Φ t z v⟩ : Bundle.TotalSpace ℂ G.line.Fiber) =
    ⟨z,(weightCharacter μ t : ℂ) • v⟩

/-- All actual real fiber weights, not weights of a very ample power. -/
def realFixedFiberWeights
    (Φ : ∀ t z, G.line.Fiber z ≃ₗ[ℂ] G.line.Fiber (a t z)) :
    Set (Fin r → ℝ) :=
  {w | ∃ z μ, w = (fun i => (μ i : ℝ)) ∧ FixedFiberCharacter IR G a Φ z μ}

/-- Every literal extremal connected fixed component is a single point. -/
def HasIsolatedExtremalComponents
    (Φ : ∀ t z, G.line.Fiber z ≃ₗ[ℂ] G.line.Fiber (a t z)) : Prop :=
  ∀ z μ, (∀ t, a t z = z) → FixedFiberCharacter IR G a Φ z μ →
    (fun i => (μ i : ℝ)) ∈
      (convexHull ℝ (realFixedFiberWeights IR G a Φ)).extremePoints ℝ →
    (connectedComponentIn {x : Z | ∀ t, a t x = x} z).Subsingleton

/-- Reviewed analytic ORSW 5.1 with literal group, line, maximality and
fixed-component hypotheses. No lower-dimensional classification is assumed. -/
def AnalyticCompactRealFormExtremalRecognition : Prop :=
  ∀ {R H Z : Type}
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
    (IR : ModelWithCorners ℝ R H) [IsManifold IR ∞ Z]
    [CompactSpace Z] [T2Space Z] [SecondCountableTopology Z] [ConnectedSpace Z]
    (n : ℕ) (_hn : 1 ≤ n)
    (G : ContactGeometry (IR := IR) (Z := Z) n)
    (D : Z → Submodule ℂ (ComplexTwistorModel n)),
    ContactGeometry.IsComplexContactKernel IR G D →
    letI := G.charts
    letI := G.complexManifold
    AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (ContactGeometry.lineCore IR G) →
    Function.Bijective (fun q : ℤ =>
      (Quotient.mk _ (ContactGeometry.lineCore IR G) :
        CoreClass.{0} (B := Z) 𝓘(ℂ,ComplexTwistorModel n)) ^ q) →
    ∀ {VC : Type} [NormedAddCommGroup VC] [NormedSpace ℂ VC]
      [FiniteDimensional ℂ VC] [ChartedSpace VC (Automorphisms D)]
      [IsManifold 𝓘(ℂ,VC) ∞ (Automorphisms D)]
      [LieGroup 𝓘(ℂ,VC) ∞ (Automorphisms D)],
      ContMDiff (𝓘(ℂ,VC).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : Automorphisms D × Z => p.1.1 p.2) →
      ∀ {K VR : Type} [Group K] [TopologicalSpace K] [CompactSpace K]
        [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
        [ChartedSpace VR K] [IsManifold 𝓘(ℝ,VR) ∞ K] [LieGroup 𝓘(ℝ,VR) ∞ K]
        (ι : K →* Automorphisms D),
        IsCompactRealForm (VR := VR) (VC := VC) ι →
        ∀ (r : ℕ) (T : TorusEmbedding K r), 2 ≤ r → T.IsMaximal K →
          ∀ (a : Torus r →* Equiv.Perm Z),
            (∀ t z, a t z = (ι (T.hom t)).1 z) →
            ∀ Φ : ∀ t z, G.line.Fiber z ≃ₗ[ℂ] G.line.Fiber (a t z),
              IsCanonicalContactLift IR G a Φ →
              HasIsolatedExtremalComponents IR G a Φ →
              ∀ z w : Z, ∃ f : Automorphisms D, f.1 z = w

end
end QuaternionicSymmetry.GeneralContactFanoORSWRecognitionSource
