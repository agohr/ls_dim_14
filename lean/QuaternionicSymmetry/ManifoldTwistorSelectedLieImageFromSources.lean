import QuaternionicSymmetry.ManifoldTwistorFullAutSelectedLieImage
import QuaternionicSymmetry.ManifoldQuaternionicSelectedTorusFullMetric
import QuaternionicSymmetry.ManifoldTwistorBWW65NonprojectiveSource

/-! Source-only selected-torus Lie-image packaging on the nonprojective
branch. It retains the SAME actual quaternionic-isometry torus through
the full-metric comparison, then uses one coherent BWW65/66 witness.
This concludes self-centralization of a Lie subalgebra, not yet a
maximal connected complex torus subgroup. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedLieImageFromSources

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullMetricCoherentLieTarget
open ManifoldTwistorFullAutSelectedLieImage
open ManifoldTwistorBWW65NonprojectiveSource
open ManifoldQuaternionicSelectedTorusFullMetric
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open CompactLieMaximalTorusTangentSource
open ComplexifiedLieCentralizerComponents IdentityComponentLie
open RealToComplexTangentComplexification
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
  (hQ : FullMetricSpanPreservation P.tangent)
  (hMS : MyersSteenrodSource.{0,0})
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (B : CompatibleComplexAtlas P.tangent D n)
  (L : HolomorphicContactLine P.tangent D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
  (hMax : T.IsMaximal (QuaternionicIsometries P.tangent))

/-- A coherent actual Lie witness plus the exact self-centralizer of the
selected T's complexified derivative image. -/
def SelectedLieImageConclusion : Prop :=
  letI := B.charts
  letI := B.complexManifold
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  let Tm := selectedFullMetricTorus P n hn hDim hQ hMS T
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
                  letI : LieGroup 𝓘(ℝ,VR) ∞ (M ≃ᵢ M) := hLieR
                  letI : ChartedSpace VR (Component (M ≃ᵢ M)) :=
                    IdentityComponentLie.charts VR (M ≃ᵢ M)
                  letI : LieGroup 𝓘(ℝ,VR) ∞ (Component (M ≃ᵢ M)) :=
                    IdentityComponentLie.lieGroup VR (M ≃ᵢ M)
                  letI : LieGroup 𝓘(ℂ,VC) ∞
                      (TwistorHolomorphicAutomorphisms P.tangent D B) := hLieC
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
                  let Tc := liftToComponent (M ≃ᵢ M) Tm
                  let fℂ := complexifiedMapComplex
                    (fullMetricLiftDerivative P n hn hDim hQ hMS D B L hR3
                      hChartR hChartC)
                  let S := (complexSpan (torusLieSpan (V := VR) Tc)).map fℂ
                  CoherentLieAtAtlases P n hn hDim hQ hMS D B L hR3
                    hChartR hChartC hLieR hLieC ∧
                  (∀ z : GroupLieAlgebra 𝓘(ℂ,VC)
                      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)),
                    z ∈ S ↔ ∀ w ∈ S, ⁅z,w⁆ = 0)

include hn hDim hQ hMS hMax

theorem selected_of_coherent
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    (hCoherent : FullMetricCoherentLieConclusion
      P n hn hDim hQ hMS D B L hR3) :
    SelectedLieImageConclusion P n hn hDim hQ hMS D B L hR3
      T := by
  letI := B.charts
  letI := B.complexManifold
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  obtain ⟨VR,hNormR,hSpaceR,hFiniteR,hChartR,hLieR,
    VC,hNormC,hSpaceC,hFiniteC,hChartC,hLieC,hData⟩ := hCoherent
  refine ⟨VR,hNormR,hSpaceR,hFiniteR,hChartR,hLieR,
    VC,hNormC,hSpaceC,hFiniteC,hChartC,hLieC,hData,?_⟩
  exact selected_image_selfCentralizing
    P n hn hDim hQ hMS D B L hR3 hChartR hChartC hLieR hLieC
    hCorrespondence hData
    (selectedFullMetricTorus P n hn hDim hQ hMS T)
    (selectedFullMetricTorus_maximal P n hn hDim hQ hMS T hMax)

end
end QuaternionicSymmetry.ManifoldTwistorSelectedLieImageFromSources
