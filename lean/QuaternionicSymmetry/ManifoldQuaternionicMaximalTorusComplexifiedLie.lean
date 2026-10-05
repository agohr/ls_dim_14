import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusLie
import QuaternionicSymmetry.ComplexifiedLieCentralizerComponents

/-! The same actual maximal quaternionic-isometry torus has a
self-centralizing literal complexified tangent Lie algebra, conditional
only on the separately registered BG-L1 selected-torus correspondence.
No full twistor automorphism Lie algebra is identified here. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusComplexifiedLie

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open CompactLieMaximalTorusTangentSource
open ComplexifiedLieCentralizerComponents
open IdentityComponentLie
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
  (hCompact : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness)
  (hChart : ChartedSpace V (QuaternionicIsometries P.tangent))
  (hLie : letI : ChartedSpace V (QuaternionicIsometries P.tangent) := hChart
    LieGroup 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent))

include n hn hDim hCompact hLie

theorem selected_torus_complexified_selfCentralizing
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent)) :
    letI : ChartedSpace V (QuaternionicIsometries P.tangent) := hChart
    letI : LieGroup 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent) := hLie
    letI : ChartedSpace V (Component (QuaternionicIsometries P.tangent)) :=
      IdentityComponentLie.charts V (QuaternionicIsometries P.tangent)
    letI : LieGroup 𝓘(ℝ,V) ∞ (Component (QuaternionicIsometries P.tangent)) :=
      IdentityComponentLie.lieGroup V (QuaternionicIsometries P.tangent)
    letI : CompleteSpace V := FiniteDimensional.complete ℝ V
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
    letI : LieGroup 𝓘(ℝ,V) (minSmoothness ℝ 3)
        (Component (QuaternionicIsometries P.tangent)) :=
      LieGroup.of_le (ENat.LEInfty.out)
    let Tc := liftToComponent (QuaternionicIsometries P.tangent) T
    ∀ z : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,V)
        (Component (QuaternionicIsometries P.tangent)),
      z ∈ complexSpan (torusLieSpan (V := V) Tc) ↔
        ∀ t ∈ torusLieSpan (V := V) Tc,
          ⁅z, (1 : ℂ) ⊗ₜ[ℝ] t⁆ = 0 := by
  letI : ChartedSpace V (QuaternionicIsometries P.tangent) := hChart
  letI : LieGroup 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent) := hLie
  letI : ChartedSpace V (Component (QuaternionicIsometries P.tangent)) :=
    IdentityComponentLie.charts V (QuaternionicIsometries P.tangent)
  letI : LieGroup 𝓘(ℝ,V) ∞ (Component (QuaternionicIsometries P.tangent)) :=
    IdentityComponentLie.lieGroup V (QuaternionicIsometries P.tangent)
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  letI : LieGroup 𝓘(ℝ,V) (minSmoothness ℝ 3)
      (Component (QuaternionicIsometries P.tangent)) :=
    LieGroup.of_le (ENat.LEInfty.out)
  obtain ⟨habel,hself⟩ :=
    ManifoldQuaternionicMaximalTorusLie.selected_torus_lie_selfCentralizing
      P n hn hDim hCompact hChart hLie hCorrespondence T hMax
  dsimp only
  intro z
  exact complexSpan_selfCentralizing _ habel hself z

end
end QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusComplexifiedLie
