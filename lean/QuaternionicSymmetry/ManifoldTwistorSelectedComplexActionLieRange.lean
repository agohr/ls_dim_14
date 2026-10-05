import QuaternionicSymmetry.ManifoldTwistorSelectedComplexSpanCentralizer
import QuaternionicSymmetry.ManifoldTwistorFullAutSelectedLieImage
import QuaternionicSymmetry.ManifoldTwistorSelectedLieImageDimension
import QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutDerivative
import QuaternionicSymmetry.ComplexLieCentralizerRealRange

/-! The real tangent image of the constructed complex contact torus is
exactly the real restriction of the SAME selected maximal metric torus's
complexified Lie image. This is an infinitesimal equality only: no global
subgroup equality or complex-linearity of its parametrization is inferred. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedComplexActionLieRange

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorComplexIdentityAutAction
open ManifoldTwistorComplexIdentityAutDerivative
open ManifoldTwistorSelectedComplexSpanCentralizer
open ManifoldTwistorFullMetricCoherentLieTarget
open ManifoldTwistorFullAutSelectedLieImage
open ManifoldTwistorSelectedLieImageDimension
open RealToComplexTangentComplexification
open ComplexifiedLieCentralizerComponents
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

include hn hDim hQ hMS hRealLie hComplexLie

theorem actual_complex_action_derivative_range_eq_selected_span
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    (hData : CoherentLieAtAtlases P n hn hDim hQ hMS D B C.line hR3
      hRealChart hComplexChart hRealLie hComplexLie)
    {r d : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent))
    (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal P.tangent))
    (hJoint : letI := B.charts
      ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
        𝓘(ℂ, ComplexTwistorModel n) ∞
        (fun p : ComplexTorus r × SphereBundleTotal P.tangent => ρ p.1 p.2))
    (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal P.tangent),
      ρ (compactInclusion r t) z =
        sphereTotalMap P.tangent
          ((actionOfEmbedding P.tangent T).representation t) z)
    (hInj : Function.Injective
      (ManifoldTwistorComplexFullAutAction.complexFullAutAction P.tangent D B C
        (actionOfEmbedding P.tangent T) ρ hJoint hRestrict))
    (g : letI : MetricSpace M := riemannianMetricSpace P.tangent
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
      letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
      letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hRealLie
      letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
        IdentityComponentLie.charts VR (M ≃ᵢ M)
      EmbeddedRealLieAtlas VR (Fin r → Circle) (Component (M ≃ᵢ M))
        (liftToComponent (M ≃ᵢ M)
          (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom d) :
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
    LinearMap.range ((mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC)
      (complexIdentityAutAction P.tangent D B C
        (actionOfEmbedding P.tangent T) ρ hJoint hRestrict) 1).toLinearMap) =
      S.restrictScalars ℝ := by
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
  let f := fullMetricLiftDerivative P n hn hDim hQ hMS D B C.line hR3
    hRealChart hComplexChart
  let S := (complexSpan (torusLieSpan (V := VR) Tc)).map
    (complexifiedMapComplex f)
  have hSmooth := hData.1
  have hSelf := selected_image_selfCentralizing
    P n hn hDim hQ hMS D B C.line hR3
    hRealChart hComplexChart hRealLie hComplexLie
    hCorrespondence hData (selectedFullMetricTorus P n hn hDim hQ hMS T)
    (selectedFullMetricTorus_maximal P n hn hDim hQ hMS T hMax)
  have hRank := selected_image_finrank
    P n hn hDim hQ hMS D B C.line hR3
    hRealChart hComplexChart hRealLie hComplexLie
    hClosed hImm hLee hData
    (selectedFullMetricTorus P n hn hDim hQ hMS T)
  letI : FiniteDimensional ℝ
      (GroupLieAlgebra 𝓘(ℝ,VR) (Component (M ≃ᵢ M))) := by
    change FiniteDimensional ℝ VR
    infer_instance
  letI : FiniteDimensional ℝ (torusLieSpan (V := VR) Tc) :=
    FiniteDimensional.finiteDimensional_submodule _
  have hInjF : Function.Injective (complexifiedMapComplex f) := hData.2.1.1
  letI : FiniteDimensional ℂ S :=
    ComplexifiedLieImageDimension.complexSpan_image_finiteDimensional
      (torusLieSpan (V := VR) Tc) (complexifiedMapComplex f) hInjF
  let gφ : (Fin r → ℂ) →ₗ[ℝ]
      GroupLieAlgebra 𝓘(ℂ,VC)
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    (mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC)
      (complexIdentityAutAction P.tangent D B C
        (actionOfEmbedding P.tangent T) ρ hJoint hRestrict) 1).toLinearMap
  have hInjective : Function.Injective gφ := by
    exact complexIdentityAutAction_derivative_injective
      P.tangent D B C (actionOfEmbedding P.tangent T) ρ hJoint hRestrict
      hComplexChart hComplexLie hClosed hImm hLee hInj 1
  have hCentral (w : Fin r → ℂ)
      (s : GroupLieAlgebra 𝓘(ℂ,VC)
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)))
      (hs : s ∈ S) :
      ⁅gφ w,s⁆ = 0 := by
    exact actual_complex_derivative_centralizes_selected_span
      P n hn hDim hQ hMS D B C hR3 hRealChart hRealLie
      hComplexChart hComplexLie hClosed hImm hLee T ρ hJoint hRestrict
      g hSmooth w s hs
  have hDimension : Module.finrank ℝ (Fin r → ℂ) =
      2 * Module.finrank ℂ S := by
    rw [hRank.1]
    simp [finrank_real_of_complex]
  dsimp only
  exact ComplexLieCentralizerRealRange.range_eq_of_selfCentralizing
    S hSelf gφ hInjective hCentral hDimension

end
end QuaternionicSymmetry.ManifoldTwistorSelectedComplexActionLieRange
