import QuaternionicSymmetry.ManifoldTwistorSelectedLieImageFromSources

/-! The direct nonprojective selected-torus Lie-image consequence, with
no T1 selection and no projective-space conclusion smuggled in. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedLieImageNonprojective

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorProjectiveException
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

theorem selectedLieImage_of_nonprojective
    (hBWW6566 : NonprojectiveFullAutCoherentLieSource)
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    (hQ : FullMetricSpanPreservation P.tangent)
    (hMS : MyersSteenrodSource.{0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hNonprojective : ¬ IsComplexProjectiveTwistor
      P.tangent P.connection A)
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent)) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    SelectedLieImageConclusion P.toPositiveQuaternionicKahlerGeometry
      n hn hDim hQ hMS P.connection A C.contact.line hR3 T := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  exact selected_of_coherent
    P.toPositiveQuaternionicKahlerGeometry n hn hDim hQ hMS
    P.connection A C.contact.line hR3 T hMax hCorrespondence
    (hBWW6566 P n hn hDim A C hQ hMS hR3 hNonprojective)

end
end QuaternionicSymmetry.ManifoldTwistorSelectedLieImageNonprojective
