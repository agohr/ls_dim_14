import QuaternionicSymmetry.GeneralLeviCivitaIsometryNaturality
import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicPointIsometry
import QuaternionicSymmetry.CompactSymplecticProjectorLeviCivita

/-! The ordinary Levi-Civita connection of the actual projector metric is
natural under every actual point reflection. The quaternionic reduction is
used only to certify that these reflections are genuine metric isometries;
its parallelism is not assumed. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaSymmetry

open Manifold Bundle
open GeneralLeviCivitaSource
open GeneralLeviCivitaIsometryNaturality
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongQuaternionicPointIsometry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_pointSymmetry_leviCivita_naturality
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ (D : CoordinateLeviCivitaConnection
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn))
      (x : ProjectiveCarrier n) (u v : EModel q),
      let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
      let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
      let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
      let F := ManifoldQuaternionicConnectionIsometrySolder.localIsometryChartMap Q f x
      let R := fderiv ℝ F y₀
      R (D.form x y₀ u v) =
        D.form (f • x) (F y₀) (R u) (R v) +
          fderiv ℝ (fderiv ℝ F) y₀ u v := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := CompactSymplecticProjectorEuclideanModel.euclideanModel_isManifold n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts_isManifold n d e q g a
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let G := smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn
  have hmetric : ∀ y (v w : TangentSpace 𝓘(ℝ,EModel q) y),
      G.inner y v w = Q.tangentMetricForm y v w := by
    intro y v w
    exact (strongQuaternionicHermitianTangent_metric_eq_projector
      hLee hDesc hImm n d e q g a hq hn y v w).symm
  intro D x u v
  exact ordinaryLeviCivita_isometry_naturality_center
    Q G hmetric D
    (pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x)
    x u v

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaSymmetry
