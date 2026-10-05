import QuaternionicSymmetry.GeneralHolomorphicDistributionUniqueFull
import QuaternionicSymmetry.ManifoldTwistorContactFullAutSubgroupTopology

/-! The actual twistor contact/full group equivalence conditional on literal
preservation of the unique contact distribution by every biholomorphism.
The BKK Picard-generator branch has not been instantiated here. -/

namespace QuaternionicSymmetry.ManifoldTwistorUniqueContactFullEquiv

open GeneralHolomorphicDistributionUniqueFull
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas
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

def FullPreservesContact : Prop :=
  letI := B.charts
  letI := B.complexManifold
  AllAutomorphismsPreserve (contactDistribution Q D B L)

def contactFullEquiv (h : FullPreservesContact Q D B L) :
    ContactAutomorphisms Q D B L ≃*
      TwistorHolomorphicAutomorphisms Q D B := by
  letI := B.charts
  letI := B.complexManifold
  exact distributionEquivFull (contactDistribution Q D B L) h

def contactFullHomeomorph (h : FullPreservesContact Q D B L) :
    ContactAutomorphisms Q D B L ≃ₜ
      TwistorHolomorphicAutomorphisms Q D B := by
  letI := B.charts
  letI := B.complexManifold
  exact distributionHomeomorphFull (contactDistribution Q D B L) h

end
end QuaternionicSymmetry.ManifoldTwistorUniqueContactFullEquiv
