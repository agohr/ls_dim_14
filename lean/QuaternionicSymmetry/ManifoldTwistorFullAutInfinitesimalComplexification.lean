import QuaternionicSymmetry.ManifoldTwistorFullAutomorphismIdentityLie
import QuaternionicSymmetry.RealToComplexTangentComplexification

/-! A literal differential criterion for the actual isometry identity-component
lift into the full twistor automorphism identity component. This file only
defines the target and extracts its tangent consequence; it does not assert
the BWW complexification theorem. In particular, the real and complex Lie
atlases are displayed, rather than silently installed by a marker. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutInfinitesimalComplexification

open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullAutomorphismIdentityComponent
open ManifoldQuaternionicSpanSymmetry
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open IdentityComponentLie RealToComplexTangentComplexification
open scoped Manifold ContDiff
noncomputable section

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  (hRealChart : ChartedSpace VR (QuaternionicIsometries Q))
  (hComplexChart : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B))

/-- The derivative of the literal identity-component lift, written in the
model spaces of its chosen real and complex Lie atlases. -/
def identityLiftRealDerivative : VR →ₗ[ℝ] VC := by
  letI : ChartedSpace VR (QuaternionicIsometries Q) := hRealChart
  letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hComplexChart
  letI : ChartedSpace VR (Component (QuaternionicIsometries Q)) :=
    IdentityComponentLie.charts VR (QuaternionicIsometries Q)
  letI : ChartedSpace VC
      (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
    ComplexIdentityComponentLie.charts VC
      (TwistorHolomorphicAutomorphisms Q D B)
  exact (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC)
    (isometryIdentityLift Q D B L hR3) 1).toLinearMap

/-- The actual homomorphism has a real-smooth differential at the group
identity and its literal complex-linear span fills the complex tangent of
the full automorphism identity component. This is an infinitesimal *part*
of complexification, not a global complexification claim. -/
def InfinitesimalComplexificationConclusion : Prop :=
  letI : ChartedSpace VR (QuaternionicIsometries Q) := hRealChart
  letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hComplexChart
  letI : ChartedSpace VR (Component (QuaternionicIsometries Q)) :=
    IdentityComponentLie.charts VR (QuaternionicIsometries Q)
  letI : ChartedSpace VC
      (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
    ComplexIdentityComponentLie.charts VC
      (TwistorHolomorphicAutomorphisms Q D B)
  ContMDiff 𝓘(ℝ,VR) 𝓘(ℝ,VC) ∞
      (isometryIdentityLift Q D B L hR3) ∧
    IsInfinitesimalComplexification
      (identityLiftRealDerivative Q D B L hR3 hRealChart hComplexChart)

theorem infinitesimal_complexification_bijective
    (h : InfinitesimalComplexificationConclusion Q D B L hR3
      hRealChart hComplexChart) :
    letI : ChartedSpace VR (QuaternionicIsometries Q) := hRealChart
    letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hComplexChart
    letI : ChartedSpace VR (Component (QuaternionicIsometries Q)) :=
      IdentityComponentLie.charts VR (QuaternionicIsometries Q)
    letI : ChartedSpace VC
        (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
      ComplexIdentityComponentLie.charts VC
        (TwistorHolomorphicAutomorphisms Q D B)
    Function.Bijective (complexifiedMap
      (identityLiftRealDerivative Q D B L hR3 hRealChart hComplexChart)) := h.2

end
end QuaternionicSymmetry.ManifoldTwistorFullAutInfinitesimalComplexification
