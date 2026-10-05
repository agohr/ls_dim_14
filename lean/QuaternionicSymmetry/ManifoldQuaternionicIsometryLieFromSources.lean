import QuaternionicSymmetry.ManifoldQuaternionicIsometryClosedFromAction
import QuaternionicSymmetry.ManifoldQuaternionicIsometryRealAtlasFromSources

/-! The actual quaternionic-isometry group is a closed Lie subgroup of the
metric-isometry group. Its Lie atlas requires no full-isometry preservation
assertion. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryLieFromSources

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicRiemannianDistance
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldQuaternionicFullIsometryEmbedding
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

theorem exists_real_lie_atlas
    (hClosed : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (hR3 : IsometryLieSource.{0,0}) :
    ∃ (V : Type) (hNorm : NormedAddCommGroup V),
      letI : NormedAddCommGroup V := hNorm
      ∃ (hSpace : NormedSpace ℝ V),
        letI : NormedSpace ℝ V := hSpace
        ∃ (hFinite : FiniteDimensional ℝ V)
          (hChart : ChartedSpace V (QuaternionicIsometries P.tangent)),
          letI : FiniteDimensional ℝ V := hFinite
          letI : ChartedSpace V (QuaternionicIsometries P.tangent) := hChart
          IsManifold 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent) ∧
          LieGroup 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent) := by
  obtain ⟨d,hChart,hManifold,hLie,_⟩ :=
    ManifoldQuaternionicIsometryClosedSubgroup.exists_quaternionic_lie_atlas_of_isometryLie
      P.tangent (hR3 P.tangent) hClosed
  exact ⟨Fin d → ℝ, inferInstance, inferInstance, inferInstance,
    hChart, hManifold, hLie⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryLieFromSources
