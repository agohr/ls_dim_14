import QuaternionicSymmetry.ManifoldRiemannianTwoTorus
import QuaternionicSymmetry.IdentityComponentMaximalTorus

/-! A sourced maximal torus, of actual rank at least two, in the full
distance-isometry group when the Killing dimension exceeds three. -/

namespace QuaternionicSymmetry.ManifoldRiemannianMaximalTorus

open ManifoldRiemannianIsometryLieInput ManifoldQuaternionicRiemannianDistance
open ManifoldQuaternionicKillingFields MetricIsometryCompactness
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section
universe uMax vMax

variable {E : Type uMax} {M : Type vMax}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem full_isometry_maximal_torus_of_killing_dimension
    (hR3 : IsometryLieSource.{uMax,vMax})
    (hR4 : KillingLieSource.{uMax,vMax})
    (hTorus : MaximalTorusSource.{0,vMax})
    (hRankOne : CompactRankOneDimensionSource.{0,vMax})
    (hdim : 3 < killingDimension Q) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    ∃ r : ℕ, 2 ≤ r ∧
      ∃ T : TorusEmbedding (M ≃ᵢ M) r, T.IsMaximal (M ≃ᵢ M) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : CompactSpace (M ≃ᵢ M) := isometryEquiv_compactSpace (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  have hEmb : Topology.IsEmbedding (isometryEquivToPairs (X := M)) :=
    ⟨⟨rfl⟩,(isometryEquivPairsEquiv (X := M)).injective⟩
  letI : T2Space (M ≃ᵢ M) := hEmb.t2Space
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,_hAction,hKilling⟩ :=
    isometryLieKilling_of_sources Q hR3 hR4
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  letI : SecondCountableTopology (M ≃ᵢ M) :=
    ChartedSpace.secondCountable_of_sigmaCompact V (M ≃ᵢ M)
  have hV : 3 < Module.finrank ℝ V := by
    change 3 < Module.finrank ℝ (TangentSpace 𝓘(ℝ,V) (1 : M ≃ᵢ M))
    rw [tangent_finrank_eq_killingDimension Q hChart hKilling]
    exact hdim
  apply IdentityComponentMaximalTorus.exists_full_maximal_torus_of_dimension_gt_three
    V (M ≃ᵢ M) ?_ ?_ hV
  · letI := IdentityComponentLie.charts V (M ≃ᵢ M)
    exact @hTorus V (IdentityComponentLie.Component (M ≃ᵢ M)) _ _ _ _ _
  · letI := IdentityComponentLie.charts V (M ≃ᵢ M)
    exact @hRankOne V (IdentityComponentLie.Component (M ≃ᵢ M)) _ _ _ _ _

end
end QuaternionicSymmetry.ManifoldRiemannianMaximalTorus
