import QuaternionicSymmetry.ComplexTorusCompactLieDerivativeCentralizer
import QuaternionicSymmetry.ManifoldTwistorSelectedComplexCentralizer
import QuaternionicSymmetry.ManifoldTwistorComplexFullAutRealSmooth
import QuaternionicSymmetry.ManifoldTwistorFullMetricCoherentLieTarget

/-! The actual Laurent/contact complex-torus derivative centralizes
the derivative of its SAME selected compact restriction in the genuine
full twistor automorphism Lie algebra. Compact restriction is literally
the selected ordinary metric lift, by the checked action equality.
No passage to the identity-component Lie algebra is claimed here. -/

namespace QuaternionicSymmetry.ManifoldTwistorActualFullAutLieDerivativeCentralizer

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorFullMetricCoherentLieTarget
open ManifoldTwistorComplexFullAutAction
open ManifoldTwistorComplexFullAutRealSmooth
open ManifoldQuaternionicSelectedTorusFullMetric
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open IdentityComponentLie TorusLaurentRepresentation
open ComplexTorusHolomorphicStructure
open SelectedTorusCompactInclusionSmooth
open ComplexTorusCompactLieDerivativeCentralizer
open ComplexLieRealCompanion
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E M VR VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
  (hQ : FullMetricSpanPreservation P.tangent)
  (hMS : MyersSteenrodSource.{0,0})
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (B : CompatibleComplexAtlas P.tangent D n)
  (C : HolomorphicContactData P.tangent D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  {r d : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
  (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal P.tangent))
  (hJoint : letI := B.charts
    ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
      𝓘(ℂ, ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal P.tangent => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal P.tangent),
    ρ (compactInclusion r t) z =
      sphereTotalMap P.tangent
        ((actionOfEmbedding P.tangent T).representation t) z)
  (hComplexChart : letI := B.charts
    letI := B.complexManifold
    ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B))
  (hComplexLie : letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
    LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent D B))

include hComplexLie

theorem actual_complex_derivative_centralizes_selected_compact_derivative
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hTorusChart : ChartedSpace (Fin d → ℝ) (Fin r → Circle))
    (hTorusManifold : letI := hTorusChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle))
    (hTorusLie : letI := hTorusChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle))
    (hInc : letI := hTorusChart
      ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin r → ℂ) ∞
        (compactInclusion r))
    (v : Fin r → ℂ) (w : Fin d → ℝ) :
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
    letI := hTorusChart
    @Bracket.bracket
      (GroupLieAlgebra 𝓘(ℂ,VC)
        (TwistorHolomorphicAutomorphisms P.tangent D B))
      (GroupLieAlgebra 𝓘(ℂ,VC)
        (TwistorHolomorphicAutomorphisms P.tangent D B)) inferInstance
      (mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC)
        (complexFullAutAction P.tangent D B C
          (actionOfEmbedding P.tangent T) ρ hJoint hRestrict) 1 v)
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC)
        ((complexFullAutAction P.tangent D B C
          (actionOfEmbedding P.tangent T) ρ hJoint hRestrict).comp
          (compactInclusion r)) 1 w) = 0 := by
  letI := B.charts
  letI := B.complexManifold
  letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
  letI : LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexLie
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := hTorusChart
  exact compact_restriction_derivatives_commute
    (complexFullAutAction P.tangent D B C
      (actionOfEmbedding P.tangent T) ρ hJoint hRestrict)
    hTorusChart hTorusManifold hTorusLie
    (complexFullAutAction_realSmooth P.tangent D B C
      (actionOfEmbedding P.tangent T) ρ hJoint hRestrict
      hComplexChart hComplexLie hClosed hImm hLee)
    hInc v w

end
end QuaternionicSymmetry.ManifoldTwistorActualFullAutLieDerivativeCentralizer
