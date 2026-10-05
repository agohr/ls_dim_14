import QuaternionicSymmetry.ManifoldTopFormGlobalMeasure
import QuaternionicSymmetry.ManifoldQuaternionicVolume

/-! The measure canonically associated to the genuine quaternionic top form. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCanonicalVolume

open Module MeasureTheory ManifoldDifferentialForms
  ManifoldTopFormLocalMeasure ManifoldTopFormGlobalMeasure
  ManifoldQuaternionicVolume ManifoldQuaternionicMetric
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [Nontrivial E] [Nonempty M]
  [T2Space M] [CompactSpace M]

/-- Absolute integration measure of the quaternionic fundamental top wedge. -/
def quaternionicVolumeMeasure
    (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) :
    Measure M :=
  canonicalTopFormMeasure (fundamentalTopForm Q)

theorem quaternionicVolumeMeasure_restrict_chart
    (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
    (q : M) :
    (quaternionicVolumeMeasure Q).restrict (extChartAt 𝓘(ℝ, E) q).source =
      chartMeasure (fundamentalTopForm Q) q :=
  canonicalTopFormMeasure_restrict_chart (fundamentalTopForm Q)
    (fundamentalTopForm_smooth Q) q

instance quaternionicVolumeMeasure.instIsFiniteMeasure
    (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) :
    IsFiniteMeasure (quaternionicVolumeMeasure Q) :=
  canonicalTopFormMeasure_finite (fundamentalTopForm Q)
    (fundamentalTopForm_smooth Q)

/-- The canonical quaternionic volume measure gives positive mass to every
nonempty open subset of the manifold. -/
instance quaternionicVolumeMeasure.instIsOpenPosMeasure
    (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) :
    (quaternionicVolumeMeasure Q).IsOpenPosMeasure := by
  refine ⟨fun U hU hUne => ?_⟩
  obtain ⟨x, hx⟩ := hUne
  let c := extChartAt 𝓘(ℝ, E) x
  let W : Set M := U ∩ c.source
  let V : Set E := c.target ∩ c.symm ⁻¹' W
  have hsource : IsOpen c.source := isOpen_extChartAt_source x
  have htarget : IsOpen c.target := isOpen_extChartAt_target x
  have hW : IsOpen W := hU.inter hsource
  have hV : IsOpen V :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage htarget hW
  have hVne : V.Nonempty := by
    refine ⟨c x, c.map_source (mem_extChartAt_source x), ?_⟩
    change c.symm (c x) ∈ W
    rw [c.left_inv (mem_extChartAt_source x)]
    exact ⟨hx, mem_extChartAt_source x⟩
  have hVsub : V ⊆ c.target := Set.inter_subset_left
  have hpos := fundamental_coordinateMeasure_open_pos Q x hV hVne hVsub
  have hchart : 0 < chartMeasure (fundamentalTopForm Q) x W := by
    rw [chartMeasure, Measure.map_apply_of_aemeasurable
      (chartSymm_aeMeasurable (fundamentalTopForm Q) x) hW.measurableSet]
    exact lt_of_lt_of_le hpos (measure_mono Set.inter_subset_right)
  have hlocal := quaternionicVolumeMeasure_restrict_chart Q x
  have heq : quaternionicVolumeMeasure Q W =
      chartMeasure (fundamentalTopForm Q) x W := by
    calc
      quaternionicVolumeMeasure Q W =
          ((quaternionicVolumeMeasure Q).restrict c.source) W := by
        rw [Measure.restrict_apply hW.measurableSet,
          Set.inter_eq_left.mpr Set.inter_subset_right]
      _ = _ := congrArg (fun m : Measure M => m W) hlocal
  exact (lt_of_lt_of_le (heq ▸ hchart)
    (measure_mono Set.inter_subset_left)).ne'

theorem quaternionicVolumeMeasure_unique
    (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
    (μ : Measure M)
    (hμ : ∀ q : M, μ.restrict (extChartAt 𝓘(ℝ, E) q).source =
      chartMeasure (fundamentalTopForm Q) q) :
    μ = quaternionicVolumeMeasure Q := by
  apply measure_eq_of_chart_restrict (E := E)
  intro q
  exact (hμ q).trans (quaternionicVolumeMeasure_restrict_chart Q q).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicCanonicalVolume
