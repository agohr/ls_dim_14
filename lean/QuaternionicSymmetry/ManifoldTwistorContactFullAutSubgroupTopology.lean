import QuaternionicSymmetry.GeneralHolomorphicContactSubgroupTopology
import QuaternionicSymmetry.ManifoldTwistorFullAutomorphisms

/-! The genuine twistor contact-automorphism group is topologically embedded
in the genuine full biholomorphism group, in their already defined topologies.
No analytic Lie-subgroup structure is inferred. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactFullAutSubgroupTopology

open GeneralHolomorphicContactSubgroupTopology
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas
open Topology
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

theorem contactForget_isEmbedding :
    IsEmbedding (contactForget Q D B L) := by
  letI := B.charts
  letI := B.complexManifold
  exact forgetDistribution_isEmbedding (contactDistribution Q D B L)

end
end QuaternionicSymmetry.ManifoldTwistorContactFullAutSubgroupTopology
