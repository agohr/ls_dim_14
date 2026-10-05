import QuaternionicSymmetry.ManifoldTwistorFullAutomorphisms
import QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput
import QuaternionicSymmetry.ManifoldQuaternionicJointSphereContinuity

/-! The actual isometry lift lands faithfully and continuously in the
full biholomorphism group, as used in BWW Theorem 6.5. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutomorphismLift

open GeneralHolomorphicFullAutomorphisms
open GeneralHolomorphicDistributionAutomorphismTopology
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorContactAutomorphisms
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicJointSphereContinuity
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
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

def isometryFullLift : QuaternionicIsometries Q →*
    TwistorHolomorphicAutomorphisms Q D B :=
  (contactForget Q D B L).comp (isometryContactLift Q D B L)

theorem isometryFullLift_injective :
    Function.Injective (isometryFullLift Q D B L) :=
  (contactForget_injective Q D B L).comp (isometryContactLift_injective Q D B L)

theorem isometryFullLift_apply (g : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) :
    ((isometryFullLift Q D B L g).1 : SphereBundleTotal Q → SphereBundleTotal Q) z =
      ManifoldQuaternionicTwistorIsometryAction.sphereTotalMap Q g z := rfl

instance [CompactSpace M] [T2Space M] :
    IsTopologicalGroup (TwistorHolomorphicAutomorphisms Q D B) := by
  letI := B.charts
  letI := B.complexManifold
  unfold TwistorHolomorphicAutomorphisms HolomorphicAutomorphisms
  infer_instance

variable [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]

theorem isometryFullLift_continuous
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0}) :
    Continuous (isometryFullLift Q D B L) := by
  letI := B.charts
  letI := B.complexManifold
  apply continuous_representation_of_action (fullDistribution
    (V := ComplexTwistorModel n) (Z := SphereBundleTotal Q))
    (isometryFullLift Q D B L)
  exact continuous_jointSphereTotalMap Q hR3

end
end QuaternionicSymmetry.ManifoldTwistorFullAutomorphismLift
