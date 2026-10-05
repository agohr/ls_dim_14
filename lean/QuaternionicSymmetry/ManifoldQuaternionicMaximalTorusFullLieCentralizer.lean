import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusLie
import QuaternionicSymmetry.IdentityComponentTorusSelfCentralizingFull

/-! The actual selected maximal quaternionic-isometry torus is already
self-centralizing in the full real Lie algebra. BG-L1 is used only on the
connected component; open-subgroup tangent/bracket/curve-span comparisons
are proved internally. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusFullLieCentralizer

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open IdentityComponentTorusSelfCentralizingFull
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem selected_torus_full_lie_selfCentralizing
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hCompact : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness)
    (hChart : ChartedSpace V (QuaternionicIsometries P.tangent))
    (hLie : letI := hChart
      LieGroup 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent))
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent)) :
    letI := hChart
    letI := hLie
    (∀ x ∈ torusLieSpan (V := V) T,
      ∀ y ∈ torusLieSpan (V := V) T, ⁅x,y⁆ = 0) ∧
    (∀ x : GroupLieAlgebra 𝓘(ℝ,V) (QuaternionicIsometries P.tangent),
      (∀ y ∈ torusLieSpan (V := V) T, ⁅x,y⁆ = 0) →
        x ∈ torusLieSpan (V := V) T) := by
  letI : ChartedSpace V (QuaternionicIsometries P.tangent) := hChart
  letI : LieGroup 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent) := hLie
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  obtain ⟨hAb,hSelf⟩ :=
    ManifoldQuaternionicMaximalTorusLie.selected_torus_lie_selfCentralizing
      P n hn hDim hCompact hChart hLie hCorrespondence T hMax
  exact full_torus_selfCentralizing_of_component (V := V) T hAb hSelf

end
end QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusFullLieCentralizer
