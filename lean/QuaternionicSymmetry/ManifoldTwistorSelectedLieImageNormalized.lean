import QuaternionicSymmetry.ManifoldTwistorSelectedLieImageFromSources

/-! T1 plus the corrected BWW65/66 source contract yields an explicit
projective alternative or the genuine selected maximal-torus Lie image
on the actual normalized positive quaternionic-Kähler twistor. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedLieImageNormalized

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorPositiveRicciInput ManifoldTwistorProjectiveException
open ManifoldTwistorBWW65NonprojectiveSource
open ManifoldTwistorSelectedLieImageFromSources
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T3Space M] [SecondCountableTopology M] [Nonempty M]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)

theorem exists_normalized_projective_or_selectedLieImage
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hBWW6566 : NonprojectiveFullAutCoherentLieSource)
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    (hQ : FullMetricSpanPreservation P.tangent)
    (hMS : MyersSteenrodSource.{0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent))
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
          SelectedLieImageConclusion P.toPositiveQuaternionicKahlerGeometry
            n hn hDim hQ hMS P.connection A C.contact.line hR3 T := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  obtain ⟨A,C,hSplit⟩ := exists_normalized_projective_or_coherentLie
    hT1 hBWW6566 hMS hR3 P hQ n hn hDim hScalar
  refine ⟨A,C,?_⟩
  rcases hSplit with hProjective | hCoherent
  · exact Or.inl hProjective
  · exact Or.inr (selected_of_coherent
      P.toPositiveQuaternionicKahlerGeometry n hn hDim hQ hMS
      P.connection A C.contact.line hR3 T hMax
      hCorrespondence hCoherent)

end
end QuaternionicSymmetry.ManifoldTwistorSelectedLieImageNormalized
