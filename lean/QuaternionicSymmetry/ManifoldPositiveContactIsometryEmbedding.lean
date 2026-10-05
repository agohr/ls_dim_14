import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismTopology
import QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput

/-! Actual positive quaternionic metric isometries embed as a compact,
closed subgroup of the genuine holomorphic contact-automorphism group.
This is not a maximal compact subgroup or complexification theorem. -/

namespace QuaternionicSymmetry.ManifoldPositiveContactIsometryEmbedding

open ManifoldTwistorContactAutomorphisms ManifoldTwistorContactAutomorphismTopology
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldTwistorLeBrunComplexAtlas
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem isometryContactLift_isClosedEmbedding
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hQ : FullMetricSpanPreservation P.tangent)
    (hMS : ManifoldRiemannianMyersSteenrodInput.MyersSteenrodSource.{0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (L : HolomorphicContactLine P.tangent P.connection n B) :
    Topology.IsClosedEmbedding (isometryContactLift P.tangent P.connection B L) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : CompactSpace (QuaternionicIsometries P.tangent) :=
    quaternionicIsometries_compactSpace P.toPositiveQuaternionicKahlerGeometry
      n hn hDim hQ hMS
  exact (isometryContactLift_continuous P.tangent P.connection B L hR3).isClosedEmbedding
    (isometryContactLift_injective P.tangent P.connection B L)

theorem isCompact_contactIsometryImage
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hQ : FullMetricSpanPreservation P.tangent)
    (hMS : ManifoldRiemannianMyersSteenrodInput.MyersSteenrodSource.{0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (L : HolomorphicContactLine P.tangent P.connection n B) :
    IsCompact (Set.range (isometryContactLift P.tangent P.connection B L)) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : CompactSpace (QuaternionicIsometries P.tangent) :=
    quaternionicIsometries_compactSpace P.toPositiveQuaternionicKahlerGeometry
      n hn hDim hQ hMS
  exact isCompact_range
    (isometryContactLift_continuous P.tangent P.connection B L hR3)

end
end QuaternionicSymmetry.ManifoldPositiveContactIsometryEmbedding
