import QuaternionicSymmetry.GeneralLeviCivitaCoordinateKoszul
import QuaternionicSymmetry.ManifoldQuaternionicCoordinateMetricity

/-! For a metric equal to an actual adapted tangent-frame metric, the
ordinary Levi-Civita chart metric is exactly the already constructed
solder-coordinate metric. This is a metric identity, not a connection or
quaternionic-parallelism premise. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaAdaptedMetricBridge

open Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateMetricity
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem chartMetric_eq_coordinateMetric
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,E) x),
      g.inner x v w = Q.tangentMetricForm x v w)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (v w : E) :
    chartMetric g p y v w = coordinateMetric Q p y v w := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source :=
    (extChartAt 𝓘(ℝ,E) p).map_target hy
  have hi : x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E p) := by
    simpa only [tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ,E)] using hx
  let A := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm y
  rw [chartMetric, hmetric x, Q.tangentMetric_chart_eq (achart E p) x hi]
  rw [tangentCoordChange_toChart_eq_mfderiv (I := 𝓘(ℝ,E)) p x hx]
  have hc := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := 𝓘(ℝ,E)) hy
  have hc' : (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p) x).comp A =
      ContinuousLinearMap.id ℝ E := by
    simpa only [A, x, ModelWithCorners.range_eq_univ, mfderivWithin_univ] using hc
  have hv := congrArg (fun L : E →L[ℝ] E => L v) hc'
  have hw := congrArg (fun L : E →L[ℝ] E => L w) hc'
  change (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p) x) (A v) = v at hv
  change (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p) x) (A w) = w at hw
  have h := congrArg₂
    (fun r s : E => inner ℝ (Q.frames.toFrame (achart E p) x r)
      (Q.frames.toFrame (achart E p) x s)) hv hw
  simpa only [x, A, coordinateMetric, solder_eq_toFrame Q p y hy] using h

end
end QuaternionicSymmetry.GeneralLeviCivitaAdaptedMetricBridge
