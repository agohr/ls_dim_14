import QuaternionicSymmetry.ManifoldTwistorFullMetricCoherentLieTarget
import QuaternionicSymmetry.CompactLieMaximalTorusTangentSource
import QuaternionicSymmetry.IdentityComponentMaximalTorusReverse
import QuaternionicSymmetry.ComplexifiedLieCentralizerComponents
import QuaternionicSymmetry.LieCentralizerTransport
import QuaternionicSymmetry.SelectedTorusLieSpanDimension
import QuaternionicSymmetry.ComplexifiedLieImageDimension

/-! The SAME selected metric torus's actual complexified differential image
has complex dimension exactly its written rank, in the coherent BWW65/66
atlases. The compact torus dimension is proved internally from the registered
general Lie inputs; no rank or maximality assumption is substituted. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedLieImageDimension

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

theorem selected_image_finrank
    (hClosed : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (hLee : GeneralSmoothMapSource.LeeEmbeddedCodomainRestrictionTheorem)
    (hData : CoherentLieAtAtlases P n hn hDim hQ hMS D B L hR3
      hRealChart hComplexChart hRealLie hComplexLie)
    {r : ℕ}
    (T : letI : MetricSpace M := riemannianMetricSpace P.tangent
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      TorusEmbedding (M ≃ᵢ M) r) :
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
    Module.finrank ℂ S = r ∧ Module.finrank ℝ S = 2 * r := by
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
  obtain ⟨_hSmooth,hBij,_hBracket,_hRed⟩ := hData
  have hRank := SelectedTorusLieSpanDimension.finrank_torusLieSpan_from_sources
    (V := VR) (liftToComponent (M ≃ᵢ M) T) hClosed hImm hLee
  dsimp only
  constructor
  · rw [ComplexifiedLieImageDimension.finrank_complexSpan_image _ _ hBij.1]
    exact hRank
  · rw [ComplexifiedLieImageDimension.finrank_real_complexSpan_image _ _ hBij.1]
    exact congrArg (2 * ·) hRank

end
end QuaternionicSymmetry.ManifoldTwistorSelectedLieImageDimension
