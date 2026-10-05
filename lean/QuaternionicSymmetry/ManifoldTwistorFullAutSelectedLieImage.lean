import QuaternionicSymmetry.ManifoldTwistorFullMetricCoherentLieTarget
import QuaternionicSymmetry.CompactLieMaximalTorusTangentSource
import QuaternionicSymmetry.IdentityComponentMaximalTorusReverse
import QuaternionicSymmetry.ComplexifiedLieCentralizerComponents
import QuaternionicSymmetry.LieCentralizerTransport

/-! At the coherent BWW65/66 Lie atlases, the actual selected ordinary
metric maximal torus has self-centralizing complexified Lie image in the
full twistor automorphism Lie algebra. This is a Lie-algebra statement,
not yet integration to a maximal complex torus subgroup. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutSelectedLieImage

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorFullMetricCoherentLieTarget
open RealToComplexTangentComplexification
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open CompactLieMaximalTorusTangentSource
open IdentityComponentLie IdentityComponentMaximalTorusReverse
open ComplexifiedLieCentralizerComponents LieCentralizerTransport
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
  (L : HolomorphicContactLine P.tangent D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  (hRealChart : letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    ChartedSpace VR (M ≃ᵢ M))
  (hComplexChart : letI := B.charts
    letI := B.complexManifold
    ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B))
  (hRealLie : letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
    LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M))
  (hComplexLie : letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B) :=
      hComplexChart
    LieGroup 𝓘(ℂ,VC) ∞ (TwistorHolomorphicAutomorphisms P.tangent D B))

include hn hDim hQ hMS hRealLie hComplexLie

theorem selected_image_selfCentralizing
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    (hData : CoherentLieAtAtlases P n hn hDim hQ hMS D B L hR3
      hRealChart hComplexChart hRealLie hComplexLie)
    {r : ℕ}
    (T : letI : MetricSpace M := riemannianMetricSpace P.tangent
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      TorusEmbedding (M ≃ᵢ M) r)
    (hMax : letI : MetricSpace M := riemannianMetricSpace P.tangent
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      T.IsMaximal (M ≃ᵢ M)) :
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
    let Tc := liftToComponent (M ≃ᵢ M) T
    let fℂ := complexifiedMapComplex
      (fullMetricLiftDerivative P n hn hDim hQ hMS D B L hR3
        hRealChart hComplexChart)
    let S := (complexSpan (torusLieSpan (V := VR) Tc)).map fℂ
    ∀ z : GroupLieAlgebra 𝓘(ℂ,VC)
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)),
      z ∈ S ↔ ∀ w ∈ S, ⁅z,w⁆ = 0 := by
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
  letI : ConnectedSpace (Component (M ≃ᵢ M)) := IdentityComponentLie.connected _
  letI : CompactSpace (Component (M ≃ᵢ M)) := IdentityComponentLie.compact _
  letI : SecondCountableTopology (Component (M ≃ᵢ M)) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
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
  obtain ⟨habel,hself⟩ := hCorrespondence VR (Component (M ≃ᵢ M))
    (liftToComponent (M ≃ᵢ M) T) (maximal_in_component_of_full _ T hMax)
  obtain ⟨_hSmooth,hBij,hBracket,_hRed⟩ := hData
  dsimp only
  intro z
  exact map_selfCentralizing _ hBij hBracket _
    (complexSpan_selfCentralizing_full _ habel hself) z

end
end QuaternionicSymmetry.ManifoldTwistorFullAutSelectedLieImage
