import QuaternionicSymmetry.GeneralComplexContactHomogeneousAction
import QuaternionicSymmetry.ManifoldTwistorGeneralContactInstantiation
import QuaternionicSymmetry.ManifoldTwistorBWW66ReductivitySource
import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

/-! A precisely bounded source interface for the *derived* low-dimensional
homogeneity corollary: BWW Theorem 1.2 classifies contact Fano manifolds of
complex dimension 3, 5, 7, or 9 with reductive automorphism group as
homogeneous; BWW Theorem 6.6 supplies reductivity for the selected positive
quaternionic-Kähler twistor. The usual Lie-group orbit theorem turns a
transitive holomorphic action into a submersive orbit map. We retain the
actual compatible twistor atlas, its actual contact quotient, full
biholomorphism group, and the finite-dimensional complex group atlas.

The proposition below is a **source contract**, not a theorem proved here.
In particular, `AmpleCore` and reductivity are explicit inputs; neither
the desired global-generation statement nor a Wolf-model flag is assumed.
Its output is an action witness, from which global generation follows by
the separate internal differentiation theorem. -/

namespace QuaternionicSymmetry.ManifoldTwistorBWW12HomogeneitySource

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorSphereCore
open ManifoldTwistorFullAutReductiveLieTarget
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineCorePullback
open GeneralComplexContactData
open scoped Manifold ContDiff

noncomputable section

/-- BWW 1.2 + 6.6 and the homogeneous Lie-orbit submersion theorem,
specialized to an actual selected positive quaternionic-Kähler twistor
in quaternionic dimensions two through four. This is deliberately an
action-level witness from which contact-line generation follows internally. -/
def LowDimHomogeneousActionSource : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ), 2 ≤ n → n ≤ 4 → Module.finrank ℝ E = 4*n →
    ∀ (A : CompatibleComplexAtlas P.tangent P.connection n)
      (C : NondegenerateHolomorphicContactData
        P.tangent P.connection n A),
      (letI := A.charts
       letI := A.complexManifold
       AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
         (contactLineCore P.tangent P.connection C.contact.line)) →
      FullAutReductiveLieConclusion P.tangent P.connection A →
      ∃ (V : Type) (hNorm : NormedAddCommGroup V),
        letI : NormedAddCommGroup V := hNorm
        ∃ (hSpace : NormedSpace ℂ V),
          letI : NormedSpace ℂ V := hSpace
          ∃ (hFinite : FiniteDimensional ℂ V)
            (hChart : ChartedSpace V
              (TwistorHolomorphicAutomorphisms P.tangent P.connection A)),
            letI : FiniteDimensional ℂ V := hFinite
            letI : ChartedSpace V
              (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChart
            IsManifold 𝓘(ℂ,V) ∞
              (TwistorHolomorphicAutomorphisms P.tangent P.connection A) ∧
            ∃ hLie : LieGroup 𝓘(ℂ,V) ∞
                (TwistorHolomorphicAutomorphisms P.tangent P.connection A),
              letI : LieGroup 𝓘(ℂ,V) ∞
                (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLie
              ∃ hAction : ContactGeometry.HolomorphicHomogeneousFamily
                  (C.toGeneralContactGeometry P.tangent P.connection)
                  (G := TwistorHolomorphicAutomorphisms
                    P.tangent P.connection A) 𝓘(ℂ,V),
                hAction.identity = 1 ∧
                ∀ (g : TwistorHolomorphicAutomorphisms
                    P.tangent P.connection A)
                  (z : SphereBundleTotal P.tangent),
                  hAction.action (g,z) = g.1 z

/-- The sourced homogeneous action is converted internally to generating
sections of the selected, represented *intrinsic* contact quotient line.
The same-core comparison to the twistor line is a separate bridge. -/
theorem contactLine_generated_of_lowDimHomogeneity
    (hBWW : LowDimHomogeneousActionSource)
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hn4 : n ≤ 4)
    (hDim : Module.finrank ℝ E = 4*n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hFano : letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (hAut : FullAutReductiveLieConclusion P.tangent P.connection A) :
    letI := A.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (C.toGeneralContactGeometry P.tangent P.connection).contactLineCore := by
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hAction,_,_⟩ :=
    hBWW P n hn hn4 hDim A C hFano hAut
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLie
  exact ContactGeometry.contactLine_globallyGenerated_of_homogeneousFamily
    (C.toGeneralContactGeometry P.tangent P.connection) 𝓘(ℂ,V) hAction

end
end QuaternionicSymmetry.ManifoldTwistorBWW12HomogeneitySource
