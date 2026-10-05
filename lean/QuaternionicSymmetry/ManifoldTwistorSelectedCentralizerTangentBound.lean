import QuaternionicSymmetry.ComplexLieCentralizerSpanRange
import QuaternionicSymmetry.ManifoldTwistorSelectedCentralizerSmoothFactor
import QuaternionicSymmetry.ManifoldTwistorSelectedIdentityAutDerivativeAgreement
import QuaternionicSymmetry.ManifoldTwistorFullAutSelectedLieImage
import QuaternionicSymmetry.SelectedTorusLieSpanDerivativeEquality

/-! The selected closed centralizer has no tangent directions beyond the
complexified Lie image of the SAME maximal compact metric-isometry torus.
This is an actual subgroup and actual manifold derivative statement. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedCentralizerTangentBound

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricIsometryComparison
open ManifoldTwistorFullMetricCoherentLieTarget
open ManifoldTwistorFullAutSelectedLieImage
open ManifoldTwistorComplexIdentityAutAction
open ManifoldTwistorSelectedMetricCentralizer
open ManifoldTwistorSelectedIdentityAutDerivativeAgreement
open ManifoldTwistorSelectedIdentityAutCompactAgreement
open ManifoldQuaternionicSelectedTorusFullMetric
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open CompactLieMaximalTorusTangentSource
open IdentityComponentLie TorusLaurentRepresentation
open RealToComplexTangentComplexification
open ComplexifiedLieCentralizerComponents
open ComplexLieCentralizerSpanRange
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

theorem selected_centralizer_inclusion_derivative_range_le
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    (hData : CoherentLieAtAtlases P n hn hDim hQ hMS D B C.line hR3
      hRealChart hComplexChart hRealLie hComplexLie)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    {r d e : ℕ}
    (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
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
    (gT : letI : MetricSpace M := riemannianMetricSpace P.tangent
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
      letI : ChartedSpace VR (M ≃ᵢ M) := hRealChart
      letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hRealLie
      letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
        IdentityComponentLie.charts VR (M ≃ᵢ M)
      EmbeddedRealLieAtlas VR (Fin r → Circle) (Component (M ≃ᵢ M))
        (liftToComponent (M ≃ᵢ M)
          (selectedFullMetricTorus P n hn hDim hQ hMS T)).hom d)
    (gH : letI := B.charts
      letI := B.complexManifold
      letI : ChartedSpace VC
        (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
      letI : ChartedSpace VC
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
        ComplexIdentityComponentLie.charts VC
          (TwistorHolomorphicAutomorphisms P.tangent D B)
      let H := selectedMetricCentralizer P n D B C T ρ hJoint hRestrict
      EmbeddedRealLieAtlas VC H
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) H.subtype e) :
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
    letI : LieGroup 𝓘(ℝ,VR) (minSmoothness ℝ 3)
        (Component (M ≃ᵢ M)) := LieGroup.of_le (ENat.LEInfty.out)
    letI : LieGroup 𝓘(ℂ,VC) (minSmoothness ℂ 3)
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
      LieGroup.of_le (ENat.LEInfty.out)
    letI := gT.charts
    letI := gH.charts
    let Tc := liftToComponent (M ≃ᵢ M)
      (selectedFullMetricTorus P n hn hDim hQ hMS T)
    let f := fullMetricLiftDerivative P n hn hDim hQ hMS D B C.line hR3
      hRealChart hComplexChart
    let S := (complexSpan (torusLieSpan (V := VR) Tc)).map
      (complexifiedMapComplex f)
    let H := selectedMetricCentralizer P n D B C T ρ hJoint hRestrict
    LinearMap.range ((mfderiv 𝓘(ℝ,Fin e → ℝ) 𝓘(ℝ,VC)
      H.subtype 1).toLinearMap) ≤ S.restrictScalars ℝ := by
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
  letI : IsManifold 𝓘(ℝ,VC) ∞
    (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexLieRealCompanion.realManifold
  letI : LieGroup 𝓘(ℝ,VC) ∞
    (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexLieRealCompanion.realLieGroup
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
  let H := selectedMetricCentralizer P n D B C T ρ hJoint hRestrict
  letI := gT.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := gT.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := gT.lieGroup
  letI := gH.charts
  letI : IsManifold 𝓘(ℝ,Fin e → ℝ) ∞ H := gH.manifold
  letI : LieGroup 𝓘(ℝ,Fin e → ℝ) ∞ H := gH.lieGroup
  let f := fullMetricLiftDerivative P n hn hDim hQ hMS D B C.line hR3
    hRealChart hComplexChart
  let h := (complexIdentityAutAction P.tangent D B C
    (actionOfEmbedding P.tangent T) ρ hJoint hRestrict).comp
      (compactInclusion r)
  have hRange := SelectedTorusLieSpanDerivativeEquality.torusLieSpan_eq_derivative_range
    Tc gT hImm hLee
  have hSelf := selected_image_selfCentralizing
    P n hn hDim hQ hMS D B C.line hR3
    hRealChart hComplexChart hRealLie hComplexLie
    hCorrespondence hData (selectedFullMetricTorus P n hn hDim hQ hMS T)
    (selectedFullMetricTorus_maximal P n hn hDim hQ hMS T hMax)
  have hMetricSmooth := hData.1
  have hTorSmooth : ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR) ∞ Tc.hom :=
    ManifoldImmersionSmooth.smoothEmbedding_contMDiff gT.smoothEmbedding
  have hh : ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC) ∞ h := by
    change ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC) ∞
      ((complexIdentityAutAction P.tangent D B C
        (actionOfEmbedding P.tangent T) ρ hJoint hRestrict).comp
          (compactInclusion r))
    rw [compact_restriction_eq_selected_identity_lift
      P n hn hDim hQ hMS D B C hR3 T ρ hJoint hRestrict]
    exact hMetricSmooth.comp hTorSmooth
  have hDerivEq := selected_compact_derivative_eq_comp
    P n hn hDim hQ hMS D B C hR3 T ρ hJoint hRestrict
    hRealChart hRealLie hComplexChart hComplexLie gT hMetricSmooth
  have hDeriv (v : Fin d → ℝ) :
      mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC) h 1 v =
        f ((mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR) Tc.hom 1).toLinearMap v) := by
    exact congrArg (fun A : (Fin d → ℝ) →L[ℝ] VC => A v) hDerivEq
  have hHSmooth : ContMDiff 𝓘(ℝ,Fin e → ℝ) 𝓘(ℝ,VC) ∞ H.subtype :=
    ManifoldImmersionSmooth.smoothEmbedding_contMDiff gH.smoothEmbedding
  have hComm (a : H) (b : Fin r → Circle) : Commute (a :
      Component (TwistorHolomorphicAutomorphisms P.tangent D B)) (h b) := by
    have ha := a.property
    exact (ha (h b) ⟨b,rfl⟩).symm
  exact centralizer_subtype_derivative_range_le H h hHSmooth hh hComm
    (torusLieSpan (V := VR) Tc) f
    (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR) Tc.hom 1).toLinearMap
    hRange hDeriv hSelf

end
end QuaternionicSymmetry.ManifoldTwistorSelectedCentralizerTangentBound
