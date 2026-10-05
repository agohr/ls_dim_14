import QuaternionicSymmetry.ManifoldTwistorBWW65NonprojectiveSource

/-! Explicit projective-or-coherent-infinitesimal-Lie split for an arbitrary
positive compact connected quaternionic-Kähler manifold after the checked
homothety. The projective alternative is not silently discarded. -/

namespace QuaternionicSymmetry.ManifoldTwistorBWW65NonprojectiveRescaled

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldQuaternionicKSWEq38Input
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorProjectiveException
open ManifoldTwistorBWW65NonprojectiveSource
open ManifoldTwistorFullMetricCoherentLieTarget
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_rescaled_projective_or_coherentLie
    (hT1 : ManifoldTwistorPositiveRicciInput.NormalizedPositiveRicciContactExistence)
    (hBWW6566 : NonprojectiveFullAutCoherentLieSource)
    (hMS : MyersSteenrodSource.{0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hQ : ∀ s hs, FullMetricSpanPreservation (rescaleCompact P s hs).tangent)
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    ∃ s : ℝ, ∃ hs : 0 < s,
      ∃ A : CompatibleComplexAtlas
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension,
      ∃ C : NondegenerateHolomorphicContactData
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension A,
        IsComplexProjectiveTwistor
          (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection A ∨
          FullMetricCoherentLieConclusion
            (rescaleCompact P s hs).toPositiveQuaternionicKahlerGeometry
            S.quaternionicDimension hn S.real_finrank (hQ s hs) hMS
            (rescaleCompact P s hs).connection A C.contact.line hR3 := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  obtain ⟨s,hs,hScalar⟩ := exists_normalized_scalar S P heq38 hn
  obtain ⟨A,C,hSplit⟩ := exists_normalized_projective_or_coherentLie
    hT1 hBWW6566 hMS hR3 (rescaleCompact P s hs) (hQ s hs)
    S.quaternionicDimension hn S.real_finrank hScalar
  exact ⟨s,hs,A,C,hSplit⟩

end
end QuaternionicSymmetry.ManifoldTwistorBWW65NonprojectiveRescaled
