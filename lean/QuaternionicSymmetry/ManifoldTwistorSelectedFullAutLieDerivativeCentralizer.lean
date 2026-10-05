import QuaternionicSymmetry.ManifoldTwistorActualFullAutLieDerivativeCentralizer
import QuaternionicSymmetry.SelectedTorusEmbeddedLieAtlas

/-! Discharge the compact-inclusion smoothness hypothesis for the SAME
selected ordinary-metric torus equipped with its actual BG-L3 atlas.
The resulting commutation is in the actual full-Aut complex Lie algebra. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedFullAutLieDerivativeCentralizer

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorComplexFullAutAction
open ManifoldTwistorActualFullAutLieDerivativeCentralizer
open ManifoldQuaternionicSelectedTorusFullMetric
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open IdentityComponentLie TorusLaurentRepresentation
open ComplexTorusHolomorphicStructure
open SelectedTorusCompactInclusionSmooth
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

theorem actual_selected_complex_derivative_centralization
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
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
    (v : Fin r → ℂ) (w : Fin d → ℝ) :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
    letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hRealLie
    letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
      IdentityComponentLie.charts VR (M ≃ᵢ M)
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
    letI := g.charts
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
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
  letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hRealLie
  letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.charts VR (M ≃ᵢ M)
  letI : IsManifold 𝓘(ℝ,VR) ∞ (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.manifold VR (M ≃ᵢ M)
  letI : LieGroup 𝓘(ℝ,VR) ∞ (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.lieGroup VR (M ≃ᵢ M)
  letI : T2Space (M ≃ᵢ M) := by
    have hEmb : Topology.IsEmbedding (isometryEquivToPairs (X := M)) :=
      ⟨⟨rfl⟩,(isometryEquivPairsEquiv (X := M)).injective⟩
    exact hEmb.t2Space
  letI : T2Space (Component (M ≃ᵢ M)) := inferInstance
  letI : CompactSpace (M ≃ᵢ M) := isometryEquiv_compactSpace (X := M)
  letI : SecondCountableTopology (M ≃ᵢ M) :=
    ChartedSpace.secondCountable_of_sigmaCompact VR _
  letI : SecondCountableTopology (Component (M ≃ᵢ M)) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let Tc := liftToComponent (M ≃ᵢ M)
    (selectedFullMetricTorus P n hn hDim hQ hMS T)
  have hInc := compactInclusion_smooth Tc g hClosed hImm hLee
  exact actual_complex_derivative_centralizes_selected_compact_derivative
    P n D B C T ρ hJoint hRestrict
    hComplexChart hComplexLie hClosed hImm hLee
    g.charts g.manifold g.lieGroup hInc v w

end
end QuaternionicSymmetry.ManifoldTwistorSelectedFullAutLieDerivativeCentralizer
