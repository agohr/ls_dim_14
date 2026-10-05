import QuaternionicSymmetry.IdentityComponentLie
import QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput

/-! A faithful two-torus in the full isometry group from more than three
actual Killing fields. The only structural premises are registered general
Riemannian and compact Lie-group sources. Quaternionic preservation is not
asserted by this theorem. -/

namespace QuaternionicSymmetry.ManifoldRiemannianTwoTorus

open ManifoldRiemannianIsometryLieInput ManifoldQuaternionicRiemannianDistance
open ManifoldQuaternionicKillingFields MetricIsometryCompactness
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section
universe uTwo vTwo

variable {E : Type uTwo} {M : Type vTwo}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem full_isometry_two_torus_of_killing_dimension
    (hR3 : IsometryLieSource.{uTwo,vTwo})
    (hR4 : KillingLieSource.{uTwo,vTwo})
    (hTorus : MaximalTorusSource.{0,vTwo})
    (hRankOne : CompactRankOneDimensionSource.{0,vTwo})
    (hdim : 3 < killingDimension Q) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    Nonempty (TorusEmbedding (M ≃ᵢ M) 2) := by
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
  apply IdentityComponentLie.exists_two_torus_of_dimension_gt_three V (M ≃ᵢ M)
    ?_ ?_ hV
  · letI := IdentityComponentLie.charts V (M ≃ᵢ M)
    exact @hTorus V (IdentityComponentLie.Component (M ≃ᵢ M)) _ _ _ _ _
  · letI := IdentityComponentLie.charts V (M ≃ᵢ M)
    exact @hRankOne V (IdentityComponentLie.Component (M ≃ᵢ M)) _ _ _ _ _

end
end QuaternionicSymmetry.ManifoldRiemannianTwoTorus
