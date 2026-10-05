import QuaternionicSymmetry.ManifoldTwistorBWW66ReductivitySource

/-! The same registered BWW 6.6 conclusion for an arbitrary compact
connected positive quaternionic-Kähler input, after the already checked
actual metric homothety. No complex automorphism-group maximality or
BWW 6.5 complexification is inferred. -/

namespace QuaternionicSymmetry.ManifoldTwistorBWW66ReductivityRescaled

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldQuaternionicKSWEq38Input
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorBWW66ReductivitySource
open ManifoldTwistorFullAutReductiveLieTarget
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_rescaled_reductive_fullAut
    (hT1 : ManifoldTwistorPositiveRicciInput.NormalizedPositiveRicciContactExistence)
    (hBWW66 : FullAutReductivitySource)
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      ∃ A : CompatibleComplexAtlas
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension,
      ∃ _C : NondegenerateHolomorphicContactData
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension A,
        FullAutReductiveLieConclusion
          (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection A := by
  obtain ⟨s,hs,hScalar⟩ := exists_normalized_scalar S P heq38 hn
  obtain ⟨A,C,hReductive⟩ := exists_normalized_reductive_fullAut
    hT1 hBWW66 (rescaleCompact P s hs) S.quaternionicDimension
    hn S.real_finrank hScalar
  exact ⟨s,hs,A,C,hReductive⟩

end
end QuaternionicSymmetry.ManifoldTwistorBWW66ReductivityRescaled
