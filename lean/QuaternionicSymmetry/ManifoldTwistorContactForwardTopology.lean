import QuaternionicSymmetry.GeneralCompactHomeomorphismForwardTopology
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismTopology
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! The independently defined actual contact-automorphism topology agrees
with the ordinary forward compact-open topology on the compact twistor. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactForwardTopology

open GeneralCompactHomeomorphismForwardTopology
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorContactAutomorphismTopology
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)

/-- Literal identity of the existing pair compact-open topology with the
ordinary forward compact-open topology of actual contact automorphisms. -/
theorem contact_pairTopology_eq_forwardTopology :
    (inferInstance : TopologicalSpace (ContactAutomorphisms Q D B L)) =
      (letI := B.charts
       letI := B.complexManifold
       forwardTopology (contactDistribution Q D B L)) := by
  letI := B.charts
  letI := B.complexManifold
  exact pairTopology_eq_forwardTopology (contactDistribution Q D B L)

end QuaternionicSymmetry.ManifoldTwistorContactForwardTopology
