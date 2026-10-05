import QuaternionicSymmetry.ManifoldTopFormJacobian
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Coordinate measures associated to a smooth, nowhere-zero tangent top form. -/
namespace QuaternionicSymmetry.ManifoldTopFormLocalMeasure

open Module MeasureTheory ManifoldDifferentialForms ManifoldTopFormJacobian
  ManifoldQuaternionicMetric ManifoldQuaternionicVolume
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [Nontrivial E] [Nonempty M]

/-- The Euclidean coordinate measure weighted by the absolute coefficient of a top form. -/
def coordinateMeasure (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (p : M) : Measure E :=
  (((Module.finBasis ℝ E).addHaar : Measure E).restrict
    (extChartAt 𝓘(ℝ, E) p).target).withDensity
      (fun y => ENNReal.ofReal (chartDensity ν p y))

/-- The measure carried from a chart target to the manifold. -/
def chartMeasure (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (p : M) : Measure M :=
  Measure.map (extChartAt 𝓘(ℝ, E) p).symm (coordinateMeasure ν p)

omit [IsManifold 𝓘(ℝ, E) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [Nontrivial E] [Nonempty M] in
theorem coordinateMeasure_eq_restrict_withDensity
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (p : M) :
    coordinateMeasure ν p =
      (((Module.finBasis ℝ E).addHaar : Measure E).withDensity
        (fun y => ENNReal.ofReal (chartDensity ν p y))).restrict
          (extChartAt 𝓘(ℝ, E) p).target := by
  rw [coordinateMeasure, restrict_withDensity
    ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).measurableSet)]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [Nontrivial E] [Nonempty M] in
theorem coordinateMeasure_compl_target
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (p : M) :
    coordinateMeasure ν p (extChartAt 𝓘(ℝ, E) p).targetᶜ = 0 := by
  rw [coordinateMeasure_eq_restrict_withDensity]
  rw [Measure.restrict_apply
    ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).measurableSet.compl)]
  simp

omit [IsManifold 𝓘(ℝ, E) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [Nontrivial E] [Nonempty M] in
theorem coordinateMeasure_ae_mem_target
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (p : M) :
    ∀ᵐ y ∂coordinateMeasure ν p, y ∈ (extChartAt 𝓘(ℝ, E) p).target := by
  change ∀ᵐ y ∂(((Module.finBasis ℝ E).addHaar : Measure E).restrict
      (extChartAt 𝓘(ℝ, E) p).target).withDensity
        (fun y => ENNReal.ofReal (chartDensity ν p y)), _
  have hbase : ∀ᵐ y ∂(((Module.finBasis ℝ E).addHaar : Measure E).restrict
      (extChartAt 𝓘(ℝ, E) p).target), y ∈ (extChartAt 𝓘(ℝ, E) p).target :=
    ae_restrict_mem
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).measurableSet)
  exact (withDensity_absolutelyContinuous _ _) hbase

omit [IsManifold 𝓘(ℝ, E) ∞ M] [Nontrivial E] [Nonempty M] in
theorem chartSymm_aeMeasurable
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (p : M) :
    AEMeasurable (extChartAt 𝓘(ℝ, E) p).symm (coordinateMeasure ν p) := by
  have htarget : MeasurableSet (extChartAt 𝓘(ℝ, E) p).target :=
    (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).measurableSet
  have hbase : AEMeasurable (extChartAt 𝓘(ℝ, E) p).symm
      (((Module.finBasis ℝ E).addHaar : Measure E).restrict
        (extChartAt 𝓘(ℝ, E) p).target) :=
    (continuousOn_extChartAt_symm (I := 𝓘(ℝ, E)) p).aemeasurable₀
      htarget.nullMeasurableSet
  exact hbase.mono_ac (withDensity_absolutelyContinuous _ _)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem fundamental_chartDensity_pos
    (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    0 < chartDensity (fundamentalTopForm Q) p y := by
  have hne := fundamentalTopForm_chart_ne_zero Q p hy
  have hb := ContinuousTopFormCoefficient.eval_basis_ne_zero
    (Module.finBasis ℝ E) (inChartModel p (fundamentalTopForm Q) y) hne
  change 0 < |inChartModel p (fundamentalTopForm Q) y (Module.finBasis ℝ E)|
  exact abs_pos.mpr hb

omit [IsManifold 𝓘(ℝ, E) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [Nontrivial E] [Nonempty M] in
/-- A smooth chart density has finite weighted measure on a compact subset
strictly inside its coordinate target. -/
theorem coordinateMeasure_compact_lt_top
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hν : ChartSmooth ν) (p : M) {K : Set E}
    (hK : IsCompact K) (hKT : K ⊆ (extChartAt 𝓘(ℝ, E) p).target) :
    coordinateMeasure ν p K < (⊤ : ENNReal) := by
  let haarMeasure : Measure E := (Module.finBasis ℝ E).addHaar
  have hcont : ContinuousOn (chartDensity ν p) K :=
    (chartDensity_continuousOn ν hν p).mono hKT
  have hbounded : BddAbove ((fun y => (chartDensity ν p y).toNNReal) '' K) :=
    hK.bddAbove_image (continuous_real_toNNReal.comp_continuousOn hcont)
  have hfinite : (haarMeasure.restrict (extChartAt 𝓘(ℝ, E) p).target) K ≠ ⊤ := by
    rw [Measure.restrict_apply hK.measurableSet]
    rw [Set.inter_eq_left.mpr hKT]
    exact hK.measure_lt_top.ne
  change (haarMeasure.restrict (extChartAt 𝓘(ℝ, E) p).target).withDensity
      (fun y => ENNReal.ofReal (chartDensity ν p y)) K < (⊤ : ENNReal)
  rw [withDensity_apply _ hK.measurableSet]
  exact setLIntegral_lt_top_of_bddAbove hfinite hbounded

omit [MeasurableSpace M] [BorelSpace M] in
/-- The quaternionic top-form density is strictly positive on each open
subset of a chart target. -/
theorem fundamental_coordinateMeasure_open_pos
    (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
    (p : M) {U : Set E} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUT : U ⊆ (extChartAt 𝓘(ℝ, E) p).target) :
    0 < coordinateMeasure (fundamentalTopForm Q) p U := by
  let base : Measure E := ((Module.finBasis ℝ E).addHaar : Measure E).restrict
    (extChartAt 𝓘(ℝ, E) p).target
  let f : E → ENNReal := fun y => ENNReal.ofReal
    (chartDensity (fundamentalTopForm Q) p y)
  have hf : AEMeasurable f base := by
    have hc : ContinuousOn f (extChartAt 𝓘(ℝ, E) p).target :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (chartDensity_continuousOn (fundamentalTopForm Q)
          (fundamentalTopForm_smooth Q) p)
    exact hc.aemeasurable₀
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).measurableSet.nullMeasurableSet)
  have hfnz : ∀ᵐ y ∂base, f y ≠ 0 := by
    filter_upwards [ae_restrict_mem
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).measurableSet)] with y hy
    exact (ENNReal.ofReal_pos.mpr (fundamental_chartDensity_pos Q p y hy)).ne'
  have hac : base ≪ coordinateMeasure (fundamentalTopForm Q) p := by
    change base ≪ base.withDensity f
    exact withDensity_absolutelyContinuous' hf hfnz
  have hbase : 0 < base U := by
    rw [Measure.restrict_apply hU.measurableSet, Set.inter_eq_left.mpr hUT]
    exact hU.measure_pos (μ := (Module.finBasis ℝ E).addHaar) hUne
  exact pos_iff_ne_zero.mpr (fun hzero => hbase.ne' (hac hzero))

end
end QuaternionicSymmetry.ManifoldTopFormLocalMeasure
