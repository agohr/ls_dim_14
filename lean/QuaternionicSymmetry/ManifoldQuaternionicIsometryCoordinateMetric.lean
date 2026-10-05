import QuaternionicSymmetry.GeneralLeviCivitaAdaptedMetricBridge
import QuaternionicSymmetry.ManifoldQuaternionicConnectionIsometrySolder

/-! Coordinate metric covariance under a genuine quaternionic isometry,
derived from its actual adapted derivative and solder covariance. The
statement is independent of every connection. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryCoordinateMetric

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryAdaptedOrthogonal
open ManifoldQuaternionicIsometryLocalDerivative
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateMetric_isometry
    (f : QuaternionicIsometries Q) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : f • ((extChartAt 𝓘(ℝ,E) p).symm y) ∈
      (extChartAt 𝓘(ℝ,E) (f • p)).source)
    (v w : E) :
    coordinateMetric Q p y v w =
      coordinateMetric Q (f • p) (localIsometryChartMap Q f p y)
        (fderiv ℝ (localIsometryChartMap Q f p) y v)
        (fderiv ℝ (localIsometryChartMap Q f p) y w) := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source :=
    (extChartAt 𝓘(ℝ,E) p).map_target hy
  have hxy : extChartAt 𝓘(ℝ,E) p x = y :=
    (extChartAt 𝓘(ℝ,E) p).right_inv hy
  have hR := localIsometryChartMap_fderiv Q f p x
    (by simpa only [extChartAt_source] using hx)
    (by simpa only [extChartAt_source] using ht)
  rw [hxy] at hR
  let S := solder Q p y
  let A := localAdaptedDerivative Q f p x
  have horth := localAdaptedDerivative_inner_on_overlap Q f p x
    (by simpa only [extChartAt_source] using hx)
    (by simpa only [extChartAt_source] using ht)
    (S v) (S w)
  have hv := localAdaptedDerivative_solder_covariant Q f p x
    (by simpa only [extChartAt_source] using hx)
    (by simpa only [extChartAt_source] using ht) v
  have hw := localAdaptedDerivative_solder_covariant Q f p x
    (by simpa only [extChartAt_source] using hx)
    (by simpa only [extChartAt_source] using ht) w
  rw [hxy, ← hR] at hv hw
  change inner ℝ (A (S v)) (A (S w)) = inner ℝ (S v) (S w) at horth
  change inner ℝ (S v) (S w) =
    inner ℝ
      (solder Q (f • p) (extChartAt 𝓘(ℝ,E) (f • p) (f • x))
        (fderiv ℝ (localIsometryChartMap Q f p) y v))
      (solder Q (f • p) (extChartAt 𝓘(ℝ,E) (f • p) (f • x))
        (fderiv ℝ (localIsometryChartMap Q f p) y w))
  rw [← hv, ← hw]
  exact horth.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryCoordinateMetric
