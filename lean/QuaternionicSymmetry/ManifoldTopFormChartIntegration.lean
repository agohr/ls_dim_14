import QuaternionicSymmetry.ManifoldTopFormMeasureTransition
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Real Bochner integration in the actual measure associated to one chart. -/
namespace QuaternionicSymmetry.ManifoldTopFormChartIntegration

open MeasureTheory Measure ManifoldDifferentialForms ManifoldTopFormJacobian
  ManifoldTopFormLocalMeasure ManifoldTopFormMeasureTransition
open scoped Manifold ContDiff Topology
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [Nontrivial E] [Nonempty M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [Nontrivial E] [Nonempty M] in
theorem integral_chartMeasure
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (hν : ChartSmooth ν)
    (p : M) (F : M → ℝ) (hF : Continuous F) :
    (∫ x, F x ∂chartMeasure ν p) =
      ∫ y in (extChartAt 𝓘(ℝ, E) p).target,
        F ((extChartAt 𝓘(ℝ, E) p).symm y) * chartDensity ν p y
          ∂(Module.finBasis ℝ E).addHaar := by
  rw [chartMeasure, integral_map (chartSymm_aeMeasurable ν p) hF.aestronglyMeasurable]
  unfold coordinateMeasure
  have hw : AEMeasurable (fun y => ENNReal.ofReal (chartDensity ν p y))
      ((Module.finBasis ℝ E).addHaar.restrict (extChartAt 𝓘(ℝ, E) p).target) := (ENNReal.continuous_ofReal.comp_continuousOn (chartDensity_continuousOn ν hν p)).aemeasurable₀
    ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).measurableSet.nullMeasurableSet)
  rw [integral_withDensity_eq_integral_toReal_smul₀ hw
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top) ]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [chartDensity, mul_comm]

end QuaternionicSymmetry.ManifoldTopFormChartIntegration
