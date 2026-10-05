import QuaternionicSymmetry.ManifoldQuaternionicIsometryCoordinateMetric

/-! Actual coordinate form of a metric isometry for an ordinary Riemannian
metric equal to an adapted quaternionic-frame metric. This is obtained
from smooth tangent geometry and contains no connection assumption. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaIsometryChartMetric

open Manifold Bundle GeneralLeviCivitaSource
open GeneralLeviCivitaAdaptedMetricBridge
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryCoordinateMetric
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartMetric_isometry
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,E) x),
      g.inner x v w = Q.tangentMetricForm x v w)
    (f : QuaternionicIsometries Q) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : f • ((extChartAt 𝓘(ℝ,E) p).symm y) ∈
      (extChartAt 𝓘(ℝ,E) (f • p)).source)
    (v w : E) :
    chartMetric g p y v w =
      chartMetric g (f • p) (localIsometryChartMap Q f p y)
        (fderiv ℝ (localIsometryChartMap Q f p) y v)
        (fderiv ℝ (localIsometryChartMap Q f p) y w) := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have htarget : localIsometryChartMap Q f p y ∈
      (extChartAt 𝓘(ℝ,E) (f • p)).target := by
    change extChartAt 𝓘(ℝ,E) (f • p) (f • x) ∈ _
    exact (extChartAt 𝓘(ℝ,E) (f • p)).map_source ht
  rw [chartMetric_eq_coordinateMetric Q g hmetric p y hy,
    chartMetric_eq_coordinateMetric Q g hmetric (f • p)
      (localIsometryChartMap Q f p y) htarget]
  exact coordinateMetric_isometry Q f p y hy ht v w

end
end QuaternionicSymmetry.GeneralLeviCivitaIsometryChartMetric
