import QuaternionicSymmetry.ManifoldTwistorContactAutomorphisms
import QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphismTopology
import QuaternionicSymmetry.ManifoldQuaternionicJointSphereContinuity
import QuaternionicSymmetry.CompactLieTorusInputs

/-! The actual isometry lift is a continuous faithful homomorphism into
the independently topologized holomorphic contact-automorphism group.
Every actual compact torus therefore lifts as the same-rank torus; maximality
in the complex contact group still requires a separate comparison. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactAutomorphismTopology

open GeneralHolomorphicDistributionAutomorphisms
open GeneralHolomorphicDistributionAutomorphismTopology
open ManifoldTwistorContactAutomorphisms
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicJointSphereContinuity
open ManifoldTwistorSphereCore ManifoldTwistorLeBrunComplexAtlas
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)

instance : TopologicalSpace (ContactAutomorphisms Q D B L) := by
  letI := B.charts
  letI := B.complexManifold
  exact inferInstanceAs (TopologicalSpace (Automorphisms (contactDistribution Q D B L)))

instance [T2Space M] : T2Space (ContactAutomorphisms Q D B L) := by
  letI := B.charts
  letI := B.complexManifold
  exact inferInstanceAs (T2Space (Automorphisms (contactDistribution Q D B L)))

instance [CompactSpace M] [T2Space M] :
    IsTopologicalGroup (ContactAutomorphisms Q D B L) := by
  letI := B.charts
  letI := B.complexManifold
  exact inferInstanceAs (IsTopologicalGroup (Automorphisms (contactDistribution Q D B L)))

variable [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]

theorem isometryContactLift_continuous
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0}) :
    Continuous (isometryContactLift Q D B L) := by
  letI := B.charts
  letI := B.complexManifold
  apply continuous_representation_of_action (contactDistribution Q D B L)
    (isometryContactLift Q D B L)
  exact continuous_jointSphereTotalMap Q hR3

def contactTorusEmbedding
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries Q) r) :
    TorusEmbedding (ContactAutomorphisms Q D B L) r where
  hom := (isometryContactLift Q D B L).comp T.hom
  continuous_hom := (isometryContactLift_continuous Q D B L hR3).comp T.continuous_hom
  injective_hom := (isometryContactLift_injective Q D B L).comp T.injective_hom

theorem contactTorusEmbedding_apply
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries Q) r)
    (t : Fin r → Circle) (z : SphereBundleTotal Q) :
    ((contactTorusEmbedding Q D B L hR3 T).hom t).1 z =
      sphereTotalMap Q (T.hom t) z := rfl

end
end QuaternionicSymmetry.ManifoldTwistorContactAutomorphismTopology
