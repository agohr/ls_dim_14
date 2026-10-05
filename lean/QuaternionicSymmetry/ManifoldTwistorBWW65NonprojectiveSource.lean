import QuaternionicSymmetry.ManifoldTwistorFullMetricCoherentLieTarget
import QuaternionicSymmetry.ManifoldTwistorProjectiveException
import QuaternionicSymmetry.ManifoldTwistorPositiveRicciInput

/-! BWW Theorems 6.5 and 6.6 on the explicit nonprojective branch. Its literal
exceptional pair has complex twistor `CP^(2n+1)`; the hypothesis below
excludes all twistors biholomorphic to that space, a deliberately narrower
but source-faithful application. The projective branch remains separate.

The source contract is on the ordinary metric-isometry identity component,
as in the paper. This older full-group wrapper additionally assumes
preservation for the particular geometry and uses Myers–Steenrod. It is
not part of the final classification source boundary. BWW 6.5's proof gives a surjective
*immersive* complexification homomorphism, not a globally injective one;
therefore the sourced conclusion here is a complexified-derivative Lie
algebra isomorphism, not a universal group-extension property. BWW 6.6's
reductivity is stated on the very same full-Aut Lie atlas. -/

namespace QuaternionicSymmetry.ManifoldTwistorBWW65NonprojectiveSource

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorPositiveRicciInput
open ManifoldTwistorProjectiveException
open ManifoldTwistorFullMetricCoherentLieTarget
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open scoped Manifold ContDiff
noncomputable section

/-- Conditional BWW 6.5/6.6 + Myers–Steenrod contract, restricted to
the nonprojective actual twistor. It asserts the safe infinitesimal Lie
isomorphism and same-atlas reductivity on ordinary metric isometries/full
twistor `Aut`, with all comparison inputs explicit. -/
def NonprojectiveFullAutCoherentLieSource : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n),
    ∀ (A : CompatibleComplexAtlas P.tangent P.connection n)
      (C : NondegenerateHolomorphicContactData
        P.tangent P.connection n A)
      (hQ : FullMetricSpanPreservation P.tangent)
      (hMS : MyersSteenrodSource.{0,0})
      (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0}),
      letI : CompactSpace M := ⟨P.compact⟩
      letI : PreconnectedSpace M := ⟨P.connected⟩
      ¬ IsComplexProjectiveTwistor P.tangent P.connection A →
      FullMetricCoherentLieConclusion P.toPositiveQuaternionicKahlerGeometry
        n hn hDim hQ hMS
        P.connection A C.contact.line hR3

/-- T1 selects a single actual atlas/contact object. BWW 6.5/6.6 yield
the coherent Lie-algebra result in the nonprojective branch; projective
space is reported explicitly and not passed through BWW 6.5. -/
theorem exists_normalized_projective_or_coherentLie
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hBWW6566 : NonprojectiveFullAutCoherentLieSource)
    (hMS : MyersSteenrodSource.{0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hQ : FullMetricSpanPreservation P.tangent)
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      ManifoldQuaternionicScalarCurvature.localScalarCurvature
        P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData
        P.tangent P.connection n A,
        IsComplexProjectiveTwistor P.tangent P.connection A ∨
          FullMetricCoherentLieConclusion P.toPositiveQuaternionicKahlerGeometry
            n hn hDim hQ hMS P.connection A C.contact.line hR3 := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  obtain ⟨A,C,m,hm⟩ := hT1 P n hn hDim hScalar
  by_cases hProjective : IsComplexProjectiveTwistor P.tangent P.connection A
  · exact ⟨A,C,Or.inl hProjective⟩
  · exact ⟨A,C,Or.inr
      (hBWW6566 P n hn hDim A C hQ hMS hR3 hProjective)⟩

end
end QuaternionicSymmetry.ManifoldTwistorBWW65NonprojectiveSource
