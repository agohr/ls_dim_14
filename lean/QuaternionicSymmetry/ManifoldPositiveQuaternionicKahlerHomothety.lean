import QuaternionicSymmetry.ManifoldQuaternionicHomothetyScalar
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-! Actual metric homothety of natural positive quaternionic Kähler geometry. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicHomothetyReduction ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyScalar ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicKSWScalarInput ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarConstancyDerived
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def rescalePositive (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (s : ℝ) (hs : 0 < s) : PositiveQuaternionicKahlerGeometry (E := E) (M := M) where
  tangent := rescaleMetric P.tangent s (ne_of_gt hs)
  connection := rescaleConnection P.tangent P.connection s (ne_of_gt hs)
  scalar_pos := by
    intro p y hy
    rw [localScalarCurvature_rescale]
    exact mul_pos (pow_pos (inv_pos.mpr hs) 2) (P.scalar_pos p y hy)

def rescaleCompact
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (s : ℝ) (hs : 0 < s) :
    CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M) where
  toPositiveQuaternionicKahlerGeometry := rescalePositive P.toPositiveQuaternionicKahlerGeometry s hs
  compact := P.compact
  connected := P.connected

theorem exists_normalized_scalar
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
        localScalarCurvature (rescaleCompact P s hs).tangent
          (rescaleCompact P s hs).connection p y hy =
          16 * (S.quaternionicDimension : ℝ) *
            ((S.quaternionicDimension : ℝ) + 2) := by
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn
  obtain ⟨s, hs, hratio⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn P.connected
  refine ⟨s, hs, ?_⟩
  intro p y hy
  have hq : (0 : ℝ) < S.quaternionicDimension := by
    exact_mod_cast (by omega : 0 < S.quaternionicDimension)
  have hc : 0 < 16 * (S.quaternionicDimension : ℝ) *
      ((S.quaternionicDimension : ℝ) + 2) := by positivity
  have hκ := hratio p y hy
  dsimp [scalarRatio] at hκ
  have hscalar : localScalarCurvature P.tangent P.connection p y hy =
      s ^ 2 * (16 * (S.quaternionicDimension : ℝ) *
        ((S.quaternionicDimension : ℝ) + 2)) := by
    apply (div_eq_iff (ne_of_gt hc)).mp
    exact hκ.symm
  change localScalarCurvature (rescaleMetric P.tangent s (ne_of_gt hs))
    (rescaleConnection P.tangent P.connection s (ne_of_gt hs)) p y hy = _
  rw [localScalarCurvature_rescale, hscalar]
  field_simp

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerHomothety
