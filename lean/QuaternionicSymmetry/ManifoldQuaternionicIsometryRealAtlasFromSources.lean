import QuaternionicSymmetry.HomeomorphLieAtlasTransfer
import QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput
import QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput

/-! BG-R3's actual compact-open isometry atlas, pulled back along the
explicit geometry-specific preservation/Myers--Steenrod identification to the true quaternionic
isometry group. This leaf asserts the manifold atlas, not yet smoothness of
the transported group operations. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryRealAtlasFromSources

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicRiemannianDistance
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianIsometryLieInput
open MetricIsometryCompactness
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)

include n hn hDim

theorem exists_real_manifold_atlas
    (hQ : FullMetricSpanPreservation P.tangent)
    (hMS : ManifoldRiemannianMyersSteenrodInput.MyersSteenrodSource.{0,0})
    (hR3 : IsometryLieSource.{0,0}) :
    ∃ (V : Type) (hNorm : NormedAddCommGroup V),
      letI : NormedAddCommGroup V := hNorm
      ∃ (hSpace : NormedSpace ℝ V),
        letI : NormedSpace ℝ V := hSpace
        ∃ (hFinite : FiniteDimensional ℝ V)
          (hChart : ChartedSpace V (QuaternionicIsometries P.tangent)),
          letI : FiniteDimensional ℝ V := hFinite
          letI : ChartedSpace V (QuaternionicIsometries P.tangent) := hChart
          IsManifold 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨V, hNorm, hSpace, hFinite, hMetricChart, hMetricManifold, _, _⟩ :=
    hR3 P.tangent
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hMetricChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hMetricManifold
  let e := fullMetricIsometryHomeomorph P n hn hDim hQ hMS
  refine ⟨V, hNorm, hSpace, hFinite,
    HomeomorphLieAtlasTransfer.charts (V := V) e, ?_⟩
  exact HomeomorphLieAtlasTransfer.manifold (V := V) e

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryRealAtlasFromSources
