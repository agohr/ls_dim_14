import QuaternionicSymmetry.ManifoldTwistorProjectiveAmpleness
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses
import QuaternionicSymmetry.ManifoldTwistorLeBrunExistenceInput

/-! An explicitly sourced *composite analytic boundary* for ampleness of the
*selected* positive quaternionic-Kähler twistor contact line. LeBrun 1995,
Theorem 2.1 constructs a positive Kähler–Einstein contact twistor; §2 (2.2)
identifies the anticanonical line with the `(n+1)`-st contact-line power.
Beauville, "Riemannian holonomy and algebraic geometry", §4.3, explicitly
records for a compact complex contact manifold that the Fano condition is
equivalent to ampleness of the contact line. His §4.1 quaternionic-Kähler
discussion has an additional simply-connected standing assumption, so we
use LeBrun's original Theorem 2.1, not that paragraph, for the arbitrary
compact connected positive input.
Kodaira's embedding theorem ("On Kähler varieties of restricted type", 1954)
converts this into a very ample positive tensor power.

This composite interface is NOT an independent Stage 2 literature premise.
At universe zero it is now derived in `ManifoldTwistorAmpleSourceDischarge`
from actual positive-Ricci tangent data in `ManifoldTwistorPositiveRicciInput`,
the general contact canonical theorem and the general Hermitian Kodaira
theorem. The determinant metric, canonical gauge transport, positive root
and complete-linear-system comparison are all checked internally. The
definitions and conditional wrappers below are retained for compatibility;
completed downstream applications must discharge the composite premise.
This file asserts no axiom and gives no classification conclusion.

Crucially, the statement is existential in the *source-selected* complex
atlas and contact form. An arbitrary `CompatibleComplexAtlas` is not silently
declared Fano. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
open QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerHomothety
open QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input
open QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature
open QuaternionicSymmetry.ManifoldTwistorProjectiveAmpleness
open QuaternionicSymmetry.ManifoldTwistorLineCoreClasses
open QuaternionicSymmetry.GeneralComplexContactData
open scoped Manifold ContDiff Quaternion

noncomputable section

universe uE uM

/-- LeBrun 1995, Theorem 2.1 and §2 (2.2), together with the positive-root
property and Kodaira embedding theorem, expressed on the actual normalized
twistor and its *selected* holomorphic contact quotient line. Ampleness means
that a positive tensor power's genuine complete linear system is a
holomorphic embedding, including its differential; it is not a proxy flag. -/
def NormalizedAmpleContactExistence : Prop :=
  ∀ {E : Type uE} {M : Type uM}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (_hn : 2 ≤ n) (_hDim : Module.finrank ℝ E = 4 * n)
    (_hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)),
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData
        P.tangent P.connection n A,
        AmpleContactLine P.tangent P.connection C.contact.line

/-- Apply the source contract to the normalized metric. The checked
canonical tensor-power relation for this selected `C` is separately
`anticanonicalClass_eq_contactTensorIterate_of_generalContact`; we avoid
repackaging its large dependent equality inside this existential. -/
theorem exists_normalized_ample_contact
    {E : Type uE} {M : Type uM}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (hAmple : NormalizedAmpleContactExistence.{uE,uM})
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData
        P.tangent P.connection n A,
        AmpleContactLine P.tangent P.connection C.contact.line :=
  hAmple P n hn hDim hScalar

/-- The same actual ample contact line exists for the explicitly normalized
homothety of an arbitrary positive compact connected quaternionic-Kähler
input; scalar normalization is proved by the metric homothety theorem. -/
theorem exists_rescaled_ample_contact
    {E : Type uE} {M : Type uM}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (hAmple : NormalizedAmpleContactExistence.{uE,uM})
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      ∃ A : CompatibleComplexAtlas
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension,
        ∃ C : NondegenerateHolomorphicContactData
          (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
          S.quaternionicDimension A,
          AmpleContactLine (rescaleCompact P s hs).tangent
            (rescaleCompact P s hs).connection C.contact.line := by
  obtain ⟨s, hs, hScalar⟩ := exists_normalized_scalar S P heq38 hn
  let R := rescaleCompact P s hs
  obtain ⟨A, C, hL⟩ :=
    exists_normalized_ample_contact hAmple R
      S.quaternionicDimension hn S.real_finrank hScalar
  exact ⟨s, hs, A, C, hL⟩

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
