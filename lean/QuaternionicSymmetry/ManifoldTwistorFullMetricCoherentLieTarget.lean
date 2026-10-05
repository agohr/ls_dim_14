import QuaternionicSymmetry.ManifoldTwistorFullMetricIsometryComparison
import QuaternionicSymmetry.RealToComplexTangentComplexificationLinear
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.BaseChange

/-! A source-faithful *infinitesimal* target for the combined BWW 6.5/6.6
conclusions. BWW 6.5's proof obtains a surjective immersive complex-Lie
homomorphism from the compact-group complexification; it does not assert
injectivity of that global homomorphism. Thus the checked consequence here
is a Lie-algebra isomorphism, not a universal group complexification. The
same full-Aut atlas carries BWW 6.6's reductive Lie algebra. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullMetricCoherentLieTarget

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open RealToComplexTangentComplexification
open IdentityComponentLie
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
  (hQ : FullMetricSpanPreservation P.tangent)
  (hMS : MyersSteenrodSource.{0,0})
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (B : CompatibleComplexAtlas P.tangent D n)
  (L : HolomorphicContactLine P.tangent D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  (hRealChart : letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    ChartedSpace VR (M ≃ᵢ M))
  (hComplexChart : letI := B.charts
    letI := B.complexManifold
    ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B))

/-- The derivative of the actual *ordinary metric-isometry* natural lift
at identity, in explicitly displayed compatible Lie atlases. -/
def fullMetricLiftDerivative :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
    letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
      IdentityComponentLie.charts VR (M ≃ᵢ M)
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B) :=
      hComplexChart
    letI : ChartedSpace VC
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
      ComplexIdentityComponentLie.charts VC
        (TwistorHolomorphicAutomorphisms P.tangent D B)
    GroupLieAlgebra 𝓘(ℝ,VR) (Component (M ≃ᵢ M)) →ₗ[ℝ]
      GroupLieAlgebra 𝓘(ℂ,VC)
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
  letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.charts VR (M ≃ᵢ M)
  letI := B.charts
  letI := B.complexManifold
  letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B) :=
    hComplexChart
  letI : ChartedSpace VC
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.charts VC
      (TwistorHolomorphicAutomorphisms P.tangent D B)
  exact (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC)
    (fullMetricIdentityLift P n hn hDim hQ hMS D B L hR3) 1).toLinearMap

/-- On one displayed pair of real/complex Lie atlases, the actual natural
lift is smooth and its complexified derivative is a bracket-preserving
bijection. BWW 6.6 reductivity is stated on this *same* full-Aut atlas. -/
def CoherentLieAtAtlases
    [FiniteDimensional ℝ VR] [FiniteDimensional ℂ VC]
    (hRealLie : letI : MetricSpace M := riemannianMetricSpace P.tangent
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
      LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M))
    (hComplexLie : letI := B.charts
      letI := B.complexManifold
      letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B) :=
        hComplexChart
      LieGroup 𝓘(ℂ,VC) ∞ (TwistorHolomorphicAutomorphisms P.tangent D B)) : Prop :=
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
  letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hRealLie
  letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.charts VR (M ≃ᵢ M)
  letI : LieGroup 𝓘(ℝ,VR) ∞ (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.lieGroup VR (M ≃ᵢ M)
  letI := B.charts
  letI := B.complexManifold
  letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B) :=
    hComplexChart
  letI : LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexLie
  letI : ChartedSpace VC
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.charts VC
      (TwistorHolomorphicAutomorphisms P.tangent D B)
  letI : LieGroup 𝓘(ℂ,VC) ∞
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.lieGroup VC
      (TwistorHolomorphicAutomorphisms P.tangent D B)
  letI : CompleteSpace VR := FiniteDimensional.complete ℝ VR
  letI : CompleteSpace VC := FiniteDimensional.complete ℂ VC
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  letI : ENat.LEInfty (minSmoothness ℂ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  letI : LieGroup 𝓘(ℝ,VR) (minSmoothness ℝ 3) (Component (M ≃ᵢ M)) :=
    LieGroup.of_le (ENat.LEInfty.out)
  letI : LieGroup 𝓘(ℂ,VC) (minSmoothness ℂ 3)
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    LieGroup.of_le (ENat.LEInfty.out)
  let f := fullMetricLiftDerivative P n hn hDim hQ hMS D B L hR3
    hRealChart hComplexChart
  let fℂ := complexifiedMapComplex f
  ContMDiff 𝓘(ℝ,VR) 𝓘(ℝ,VC) ∞
      (fullMetricIdentityLift P n hn hDim hQ hMS D B L hR3) ∧
    Function.Bijective fℂ ∧
    (∀ x y : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,VR) (Component (M ≃ᵢ M)),
      fℂ ⁅x,y⁆ = ⁅fℂ x, fℂ y⁆) ∧
    LieAlgebra.HasCentralRadical ℂ
      (GroupLieAlgebra 𝓘(ℂ,VC)
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)))

/-- A single coherent pair of Lie atlases witnesses the two precisely
registered BWW consequences. No global universal-extension claim occurs. -/
def FullMetricCoherentLieConclusion : Prop :=
  letI := B.charts
  letI := B.complexManifold
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  ∃ (VR : Type) (hNormR : NormedAddCommGroup VR),
    letI : NormedAddCommGroup VR := hNormR
    ∃ (hSpaceR : NormedSpace ℝ VR),
      letI : NormedSpace ℝ VR := hSpaceR
      ∃ (hFiniteR : FiniteDimensional ℝ VR)
        (hChartR : ChartedSpace VR (M ≃ᵢ M)),
        letI : FiniteDimensional ℝ VR := hFiniteR
        letI : ChartedSpace VR (M ≃ᵢ M) := hChartR
        ∃ hLieR : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M),
          ∃ (VC : Type) (hNormC : NormedAddCommGroup VC),
            letI : NormedAddCommGroup VC := hNormC
            ∃ (hSpaceC : NormedSpace ℂ VC),
              letI : NormedSpace ℂ VC := hSpaceC
              ∃ (hFiniteC : FiniteDimensional ℂ VC)
                (hChartC : ChartedSpace VC
                  (TwistorHolomorphicAutomorphisms P.tangent D B)),
                letI : FiniteDimensional ℂ VC := hFiniteC
                letI : ChartedSpace VC
                    (TwistorHolomorphicAutomorphisms P.tangent D B) := hChartC
                ∃ hLieC : LieGroup 𝓘(ℂ,VC) ∞
                    (TwistorHolomorphicAutomorphisms P.tangent D B),
                  CoherentLieAtAtlases P n hn hDim hQ hMS D B L hR3
                    hChartR hChartC hLieR hLieC

end
end QuaternionicSymmetry.ManifoldTwistorFullMetricCoherentLieTarget
