import QuaternionicSymmetry.ManifoldTwistorSelectedMetricLieCentralizer
import QuaternionicSymmetry.SelectedTorusLieSpanDerivativeEquality
import QuaternionicSymmetry.ComplexifiedLieImageCentralizer

/-! The real derivative centralization for the SAME selected compact torus
extends to its actual complexified metric-isometry Lie image in the full
holomorphic-automorphism identity component. No maximality is concluded. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedComplexSpanCentralizer

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorComplexIdentityAutAction
open ManifoldTwistorSelectedMetricLieCentralizer
open ManifoldTwistorFullMetricCoherentLieTarget
open RealToComplexTangentComplexification
open ComplexifiedLieCentralizerComponents ComplexifiedLieImageCentralizer
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open CompactLieMaximalTorusTangentSource
open IdentityComponentLie TorusLaurentRepresentation
open ManifoldQuaternionicSelectedTorusFullMetric
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open scoped Manifold ContDiff TensorProduct
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
  (hRealChart : letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    ChartedSpace VR (M ≃ᵢ M))
  (hRealLie : letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
    LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M))
  (hComplexChart : letI := B.charts
    letI := B.complexManifold
    ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B))
  (hComplexLie : letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
    LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent D B))

include hRealLie hComplexLie

theorem actual_complex_derivative_centralizes_selected_span
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
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
    (g : letI : MetricSpace M := riemannianMetricSpace P.tangent
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
      letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
      letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hRealLie
      letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
        IdentityComponentLie.charts VR (M ≃ᵢ M)
      EmbeddedRealLieAtlas VR (Fin r → Circle) (Component (M ≃ᵢ M))
        (liftToComponent (M ≃ᵢ M)
          (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom d)
    (hSmooth : letI : MetricSpace M := riemannianMetricSpace P.tangent
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
      letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
      letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
        IdentityComponentLie.charts VR (M ≃ᵢ M)
      letI := B.charts
      letI := B.complexManifold
      letI : ChartedSpace VC
        (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
      letI : ChartedSpace VC
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
        ComplexIdentityComponentLie.charts VC
          (TwistorHolomorphicAutomorphisms P.tangent D B)
      ContMDiff 𝓘(ℝ,VR) 𝓘(ℝ,VC) ∞
        (fullMetricIdentityLift P n hn hDim hQ hMS D B C.line hR3))
    (v : Fin r → ℂ) :
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
    letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
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
    let Tc := liftToComponent (M ≃ᵢ M)
      (selectedFullMetricTorus P n hn hDim hQ hMS T)
    let f := fullMetricLiftDerivative P n hn hDim hQ hMS D B C.line hR3
      hRealChart hComplexChart
    let S := (complexSpan (torusLieSpan (V := VR) Tc)).map
      (complexifiedMapComplex f)
    ∀ s ∈ S,
      @Bracket.bracket
        (GroupLieAlgebra 𝓘(ℂ,VC)
          (Component (TwistorHolomorphicAutomorphisms P.tangent D B)))
        (GroupLieAlgebra 𝓘(ℂ,VC)
          (Component (TwistorHolomorphicAutomorphisms P.tangent D B))) inferInstance
        (mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC)
          (complexIdentityAutAction P.tangent D B C
            (actionOfEmbedding P.tangent T) ρ hJoint hRestrict) 1 v) s = 0 := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  letI : CompactSpace (M ≃ᵢ M) := isometryEquiv_compactSpace (X := M)
  have hEmb : Topology.IsEmbedding (isometryEquivToPairs (X := M)) :=
    ⟨⟨rfl⟩,(isometryEquivPairsEquiv (X := M)).injective⟩
  letI : T2Space (M ≃ᵢ M) := hEmb.t2Space
  letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
  letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hRealLie
  letI : SecondCountableTopology (M ≃ᵢ M) :=
    ChartedSpace.secondCountable_of_sigmaCompact VR _
  letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.charts VR (M ≃ᵢ M)
  letI : LieGroup 𝓘(ℝ,VR) ∞ (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.lieGroup VR (M ≃ᵢ M)
  letI : SecondCountableTopology (Component (M ≃ᵢ M)) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  letI := B.charts
  letI := B.complexManifold
  letI : ChartedSpace VC
    (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
  letI : LieGroup 𝓘(ℂ,VC) ∞
    (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexLie
  letI : ChartedSpace VC
    (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.charts VC _
  letI : LieGroup 𝓘(ℂ,VC) ∞
    (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.lieGroup VC _
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
  let Tc := liftToComponent (M ≃ᵢ M)
    (selectedFullMetricTorus P n hn hDim hQ hMS T)
  letI := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.lieGroup
  let f := fullMetricLiftDerivative P n hn hDim hQ hMS D B C.line hR3
    hRealChart hComplexChart
  have hRange := SelectedTorusLieSpanDerivativeEquality.torusLieSpan_eq_derivative_range
    Tc g hImm hLee
  let z : GroupLieAlgebra 𝓘(ℂ,VC)
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC)
      (complexIdentityAutAction P.tangent D B C
        (actionOfEmbedding P.tangent T) ρ hJoint hRestrict) 1 v
  have hz (w : Fin d → ℝ) :
      ⁅z, f ((mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR) Tc.hom 1).toLinearMap w)⁆ = 0 := by
    exact selected_derivative_centralizes_metric_lift
      P n hn hDim hQ hMS D B C hR3 T ρ hJoint hRestrict
      hRealChart hRealLie hComplexChart hComplexLie
      hClosed hImm hLee g hSmooth v w
  dsimp only
  intro s hs
  exact centralizes_complexified_image_of_range
    (torusLieSpan (V := VR) Tc) f
    (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR) Tc.hom 1).toLinearMap
    hRange z hz hs

end
end QuaternionicSymmetry.ManifoldTwistorSelectedComplexSpanCentralizer
