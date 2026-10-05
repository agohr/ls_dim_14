import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.CompactLieMaximalTorusTangentSource
import QuaternionicSymmetry.IdentityComponentMaximalTorusReverse
import QuaternionicSymmetry.ManifoldQuaternionicIsometryLieFromSources

/-! BG-L1's selected-torus Lie-algebra conclusion on the actual compact
quaternionic-isometry identity component. This keeps the original maximal
torus embedding and the BG-R3/BG-Q1/Myers–Steenrod atlas explicit. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusLie

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldRiemannianIsometryLieInput
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open CompactLieMaximalTorusTangentSource
open IdentityComponentLie IdentityComponentMaximalTorusReverse
open scoped Manifold ContDiff
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

theorem selected_torus_lie_selfCentralizing
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent)) :
    letI : ChartedSpace V (QuaternionicIsometries P.tangent) := hChart
    letI : LieGroup 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent) := hLie
    letI : ChartedSpace V (Component (QuaternionicIsometries P.tangent)) :=
      IdentityComponentLie.charts V (QuaternionicIsometries P.tangent)
    letI : LieGroup 𝓘(ℝ,V) ∞ (Component (QuaternionicIsometries P.tangent)) :=
      IdentityComponentLie.lieGroup V (QuaternionicIsometries P.tangent)
    let Tc := liftToComponent (QuaternionicIsometries P.tangent) T
    (∀ x ∈ torusLieSpan (V := V) Tc,
      ∀ y ∈ torusLieSpan (V := V) Tc, ⁅x,y⁆ = 0) ∧
    (∀ x : GroupLieAlgebra 𝓘(ℝ,V)
        (Component (QuaternionicIsometries P.tangent)),
      (∀ y ∈ torusLieSpan (V := V) Tc, ⁅x,y⁆ = 0) →
        x ∈ torusLieSpan (V := V) Tc) := by
  letI : ChartedSpace V (QuaternionicIsometries P.tangent) := hChart
  letI : LieGroup 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent) := hLie
  letI : CompactSpace (QuaternionicIsometries P.tangent) :=
    hCompact P n hn hDim
  letI : SecondCountableTopology (QuaternionicIsometries P.tangent) :=
    ChartedSpace.secondCountable_of_sigmaCompact V _
  letI : ChartedSpace V (Component (QuaternionicIsometries P.tangent)) :=
    IdentityComponentLie.charts V (QuaternionicIsometries P.tangent)
  letI : LieGroup 𝓘(ℝ,V) ∞ (Component (QuaternionicIsometries P.tangent)) :=
    IdentityComponentLie.lieGroup V (QuaternionicIsometries P.tangent)
  letI : ConnectedSpace (Component (QuaternionicIsometries P.tangent)) :=
    IdentityComponentLie.connected _
  letI : CompactSpace (Component (QuaternionicIsometries P.tangent)) :=
    IdentityComponentLie.compact _
  letI : SecondCountableTopology (Component (QuaternionicIsometries P.tangent)) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact hCorrespondence V (Component (QuaternionicIsometries P.tangent))
    (liftToComponent (QuaternionicIsometries P.tangent) T)
    (maximal_in_component_of_full _ T hMax)

end
end QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusLie
