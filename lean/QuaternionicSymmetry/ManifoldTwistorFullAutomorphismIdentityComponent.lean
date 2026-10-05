import QuaternionicSymmetry.ManifoldTwistorFullAutomorphismLift
import QuaternionicSymmetry.IdentityComponentLie

/-! The actual isometry identity component maps faithfully into the full
twistor biholomorphism identity component. This uses only continuous
group-homomorphism topology, not a sourced complexification claim. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutomorphismIdentityComponent

open ManifoldTwistorFullAutomorphisms ManifoldTwistorFullAutomorphismLift
open ManifoldQuaternionicSpanSymmetry IdentityComponentLie
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)

def isometryIdentityLift
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0}) :
    Component (QuaternionicIsometries Q) →*
      Component (TwistorHolomorphicAutomorphisms Q D B) := by
  letI := B.charts
  letI := B.complexManifold
  let φ := isometryFullLift Q D B L
  have hφ := isometryFullLift_continuous Q D B L hR3
  refine {
    toFun := fun g => ⟨φ g.1, ?_⟩
    map_one' := ?_
    map_mul' := ?_ }
  · have hmem : (g.1 : QuaternionicIsometries Q) ∈
        connectedComponent (1 : QuaternionicIsometries Q) := g.2
    have hImage := Continuous.image_connectedComponent_subset hφ
      (1 : QuaternionicIsometries Q)
    have hh := hImage (Set.mem_image_of_mem φ hmem)
    simpa only [map_one] using hh
  · apply Subtype.ext
    exact map_one φ
  · intro g h
    apply Subtype.ext
    exact map_mul φ g.1 h.1

theorem isometryIdentityLift_injective
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0}) :
    Function.Injective (isometryIdentityLift Q D B L hR3) := by
  intro g h heq
  apply Subtype.ext
  exact (isometryFullLift_injective Q D B L)
    (congrArg Subtype.val heq)

end
end QuaternionicSymmetry.ManifoldTwistorFullAutomorphismIdentityComponent
