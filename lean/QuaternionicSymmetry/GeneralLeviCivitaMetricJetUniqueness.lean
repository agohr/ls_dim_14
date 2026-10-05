import QuaternionicSymmetry.GeneralLeviCivitaCoordinateKoszul

/-! The ordinary Levi-Civita form at a chart point depends only on the
value and first derivative of the coordinate metric there. This is the
pointwise metric-jet bridge needed for genuine isometry naturality. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaMetricJetUniqueness

open Manifold Bundle GeneralLeviCivitaSource
open GeneralLeviCivitaCoordinateKoszul
open GeneralLeviCivitaCoordinatePositive
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem form_eq_of_chart_metric_first_jet_eq
    (g h : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (Dg : CoordinateLeviCivitaConnection g)
    (Dh : CoordinateLeviCivitaConnection h)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hvalue : ∀ v w : E, chartMetric g p y v w = chartMetric h p y v w)
    (hfirst : ∀ u v w : E,
      fderiv ℝ (fun z => chartMetric g p z v w) y u =
        fderiv ℝ (fun z => chartMetric h p z v w) y u) :
    Dg.form p y = Dh.form p y := by
  ext u v
  let z : E := Dg.form p y u v - Dh.form p y u v
  have hpair (w : E) : chartMetric g p y (Dg.form p y u v) w =
      chartMetric g p y (Dh.form p y u v) w := by
    have hg := coordinate_koszul g Dg p y u v w hy
    have hh := coordinate_koszul h Dh p y u v w hy
    rw [hfirst u v w, hfirst v u w, hfirst w u v] at hg
    rw [← hvalue (Dh.form p y u v) w] at hh
    linarith only [hg, hh]
  have hz : chartMetric g p y z z = 0 := by
    dsimp only [z]
    rw [show chartMetric g p y
        (Dg.form p y u v - Dh.form p y u v) z =
        chartMetric g p y (Dg.form p y u v) z -
          chartMetric g p y (Dh.form p y u v) z by simp [chartMetric]]
    exact sub_eq_zero.mpr (hpair z)
  by_contra hne
  have hp := chartMetric_pos g p y z hy (sub_ne_zero.mpr hne)
  linarith only [hz, hp]

end
end QuaternionicSymmetry.GeneralLeviCivitaMetricJetUniqueness
