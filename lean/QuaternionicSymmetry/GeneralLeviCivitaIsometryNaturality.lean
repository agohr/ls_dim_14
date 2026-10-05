import QuaternionicSymmetry.GeneralLeviCivitaIsometryKoszulPairing
import QuaternionicSymmetry.GeneralLeviCivitaCoordinatePositive
import QuaternionicSymmetry.ManifoldQuaternionicLocalDerivativeEquivariance

/-! Genuine naturality of the ordinary Levi-Civita Christoffel form under
an actual smooth quaternionic isometry. The proof uses only ordinary metric
compatibility and torsion, actual metric covariance, symmetric chart-map
second derivatives, and invertibility of the diffeomorphism derivative.
No quaternionic-compatible connection is assumed. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaIsometryNaturality

open Manifold Bundle GeneralLeviCivitaSource
open GeneralLeviCivitaAdaptedMetricBridge
open GeneralLeviCivitaCoordinatePositive
open GeneralLeviCivitaIsometryKoszulPairing
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryCoordinateMetric
open ManifoldQuaternionicLocalDerivativeEquivariance
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem ordinaryLeviCivita_isometry_naturality_center
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,E) x),
      g.inner x v w = Q.tangentMetricForm x v w)
    (D : CoordinateLeviCivitaConnection g)
    (f : QuaternionicIsometries Q) (p : M) (u v : E) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    let F := localIsometryChartMap Q f p
    let R := fderiv ℝ F y₀
    let S := fderiv ℝ (fderiv ℝ F) y₀
    R (D.form p y₀ u v) =
      D.form (f • p) (F y₀) (R u) (R v) + S u v := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let F := localIsometryChartMap Q f p
  let R := fderiv ℝ F y₀
  let S := fderiv ℝ (fderiv ℝ F) y₀
  let z := R (D.form p y₀ u v) -
    (D.form (f • p) (F y₀) (R u) (R v) + S u v)
  have hsrc : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hy : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have ht : f • ((extChartAt 𝓘(ℝ,E) p).symm y₀) ∈
      (extChartAt 𝓘(ℝ,E) (f • p)).source := by
    rw [hsrc]
    simp
  have hF : F y₀ = extChartAt 𝓘(ℝ,E) (f • p) (f • p) := by
    simp only [F, localIsometryChartMap, hsrc]
  have htarget : F y₀ ∈ (extChartAt 𝓘(ℝ,E) (f • p)).target := by
    rw [hF]
    exact (extChartAt 𝓘(ℝ,E) (f • p)).map_source (by simp)
  have hR : R = localRawDerivative Q f p p := by
    simpa only [R, y₀, F] using
      (localIsometryChartMap_fderiv Q f p p (by simp) (by simp))
  have hsurj : Function.Surjective R := by
    intro t
    refine ⟨localRawDerivative Q f⁻¹ (f • p) (f • p) t, ?_⟩
    rw [hR]
    exact localRawDerivative_inverse Q f p p (by simp) (by simp) t
  obtain ⟨w, hw⟩ := hsurj z
  have hpair := ordinaryLeviCivita_isometry_pairing_center
    Q g hmetric D f p u v w
  have hval := coordinateMetric_isometry Q f p y₀ hy ht
    (D.form p y₀ u v) w
  have hEq :
      ManifoldQuaternionicCoordinateMetricity.coordinateMetric Q (f • p) (F y₀)
        (R (D.form p y₀ u v)) (R w) =
      ManifoldQuaternionicCoordinateMetricity.coordinateMetric Q (f • p) (F y₀)
        (D.form (f • p) (F y₀) (R u) (R v) + S u v) (R w) := by
    exact hval.symm.trans hpair
  have hz : ManifoldQuaternionicCoordinateMetricity.coordinateMetric Q (f • p)
      (F y₀) z z = 0 := by
    rw [hw] at hEq
    change ManifoldQuaternionicCoordinateMetricity.coordinateMetric Q (f • p)
      (F y₀) (R (D.form p y₀ u v) -
        (D.form (f • p) (F y₀) (R u) (R v) + S u v)) z = 0
    simp only [ManifoldQuaternionicCoordinateMetricity.coordinateMetric,
      map_sub, inner_sub_left]
    exact sub_eq_zero.mpr hEq
  by_contra hne
  have hp : 0 < ManifoldQuaternionicCoordinateMetricity.coordinateMetric Q
      (f • p) (F y₀) z z := by
    rw [← chartMetric_eq_coordinateMetric Q g hmetric (f • p) (F y₀) htarget z z]
    exact chartMetric_pos g (f • p) (F y₀) z htarget
      (sub_ne_zero.mpr hne)
  linarith only [hz, hp]

end
end QuaternionicSymmetry.GeneralLeviCivitaIsometryNaturality
