import QuaternionicSymmetry.GeneralHolomorphicFullAutomorphisms
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismTopology

/-! The actual full biholomorphism group of the selected twistor complex
manifold, and faithful continuous inclusion of its contact subgroup. This
does not install a Lie/algebraic structure or identify identity components. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutomorphisms

open GeneralHolomorphicFullAutomorphisms
open GeneralHolomorphicDistributionAutomorphisms
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorContactAutomorphismTopology
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)

def TwistorHolomorphicAutomorphisms :=
  letI := B.charts
  letI := B.complexManifold
  HolomorphicAutomorphisms (ComplexTwistorModel n) (SphereBundleTotal Q)

instance : Group (TwistorHolomorphicAutomorphisms Q D B) := by
  letI := B.charts
  letI := B.complexManifold
  unfold TwistorHolomorphicAutomorphisms
  infer_instance

instance : TopologicalSpace (TwistorHolomorphicAutomorphisms Q D B) := by
  letI := B.charts
  letI := B.complexManifold
  unfold TwistorHolomorphicAutomorphisms
  infer_instance

def contactForget (L : HolomorphicContactLine Q D n B) :
    ContactAutomorphisms Q D B L →* TwistorHolomorphicAutomorphisms Q D B := by
  letI := B.charts
  letI := B.complexManifold
  exact forgetDistribution (contactDistribution Q D B L)

theorem contactForget_injective (L : HolomorphicContactLine Q D n B) :
    Function.Injective (contactForget Q D B L) := by
  letI := B.charts
  letI := B.complexManifold
  exact forgetDistribution_injective (contactDistribution Q D B L)

end
end QuaternionicSymmetry.ManifoldTwistorFullAutomorphisms
