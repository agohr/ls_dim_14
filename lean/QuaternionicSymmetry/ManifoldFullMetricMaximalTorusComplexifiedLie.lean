import QuaternionicSymmetry.CompactLieMaximalTorusTangentSource
import QuaternionicSymmetry.ComplexifiedLieCentralizerComponents
import QuaternionicSymmetry.IdentityComponentMaximalTorusReverse
import QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput
import QuaternionicSymmetry.MetricIsometryCompactness
import QuaternionicSymmetry.ManifoldQuaternionicRiemannianDistance

/-! The selected-torus self-centralizer on the *ordinary full metric*
isometry identity component appearing literally in BWW 6.5. -/

namespace QuaternionicSymmetry.ManifoldFullMetricMaximalTorusComplexifiedLie

open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldRiemannianIsometryLieInput
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open CompactLieMaximalTorusTangentSource
open ComplexifiedLieCentralizerComponents IdentityComponentLie
open IdentityComponentMaximalTorusReverse
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem exists_selected_fullMetric_complexified_selfCentralizing
    (hR3 : IsometryLieSource.{0,0})
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    {r : ℕ}
    (T : letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      TorusEmbedding (M ≃ᵢ M) r)
    (hMax : letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      T.IsMaximal (M ≃ᵢ M)) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    ∃ (V : Type) (hNorm : NormedAddCommGroup V),
      letI : NormedAddCommGroup V := hNorm
      ∃ (hSpace : NormedSpace ℝ V),
        letI : NormedSpace ℝ V := hSpace
        ∃ (hFinite : FiniteDimensional ℝ V)
          (hChart : ChartedSpace V (M ≃ᵢ M)),
          letI : FiniteDimensional ℝ V := hFinite
          letI : ChartedSpace V (M ≃ᵢ M) := hChart
          ∃ hLie : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M),
            letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
            letI : ChartedSpace V (Component (M ≃ᵢ M)) :=
              IdentityComponentLie.charts V (M ≃ᵢ M)
            letI : LieGroup 𝓘(ℝ,V) ∞ (Component (M ≃ᵢ M)) :=
              IdentityComponentLie.lieGroup V (M ≃ᵢ M)
            letI : CompleteSpace V := FiniteDimensional.complete ℝ V
            letI : ENat.LEInfty (minSmoothness ℝ 3) := by
              simpa only [minSmoothness_of_isRCLikeNormedField] using
                (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
            letI : LieGroup 𝓘(ℝ,V) (minSmoothness ℝ 3) (Component (M ≃ᵢ M)) :=
              LieGroup.of_le (ENat.LEInfty.out)
            let Tc := liftToComponent (M ≃ᵢ M) T
            ∀ z : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,V) (Component (M ≃ᵢ M)),
              z ∈ complexSpan (torusLieSpan (V := V) Tc) ↔
                ∀ t ∈ torusLieSpan (V := V) Tc,
                  ⁅z, (1 : ℂ) ⊗ₜ[ℝ] t⁆ = 0 := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  letI : CompactSpace (M ≃ᵢ M) := isometryEquiv_compactSpace (X := M)
  have hEmb : Topology.IsEmbedding (isometryEquivToPairs (X := M)) :=
    ⟨⟨rfl⟩, (isometryEquivPairsEquiv (X := M)).injective⟩
  letI : T2Space (M ≃ᵢ M) := hEmb.t2Space
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,_hManifold,hLie,_hAction⟩ := hR3 Q
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  letI : SecondCountableTopology (M ≃ᵢ M) :=
    ChartedSpace.secondCountable_of_sigmaCompact V _
  letI : ChartedSpace V (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.charts V (M ≃ᵢ M)
  letI : LieGroup 𝓘(ℝ,V) ∞ (Component (M ≃ᵢ M)) :=
    IdentityComponentLie.lieGroup V (M ≃ᵢ M)
  letI : ConnectedSpace (Component (M ≃ᵢ M)) := IdentityComponentLie.connected _
  letI : CompactSpace (Component (M ≃ᵢ M)) := IdentityComponentLie.compact _
  letI : SecondCountableTopology (Component (M ≃ᵢ M)) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨habel,hself⟩ := hCorrespondence V (Component (M ≃ᵢ M))
    (liftToComponent (M ≃ᵢ M) T) (maximal_in_component_of_full _ T hMax)
  refine ⟨V,hNorm,hSpace,hFinite,hChart,hLie,?_⟩
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  letI : LieGroup 𝓘(ℝ,V) (minSmoothness ℝ 3) (Component (M ≃ᵢ M)) :=
    LieGroup.of_le (ENat.LEInfty.out)
  dsimp only
  intro z
  exact complexSpan_selfCentralizing _ habel hself z

end
end QuaternionicSymmetry.ManifoldFullMetricMaximalTorusComplexifiedLie
