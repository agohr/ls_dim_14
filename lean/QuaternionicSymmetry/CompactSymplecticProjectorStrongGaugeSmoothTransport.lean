import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeAtlas
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridge
import QuaternionicSymmetry.ManifoldChartRefinementSmoothness

/-! Smoothness of maps from the actual original quotient atlas transfers to
the stronger Euclidean atlas, including maps into the compact Lie group. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeSmoothTransport

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanChartBridge
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinementSmoothness
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem contMDiffOn_strongGauge_of_original
    {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace N] [ChartedSpace H' N]
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (f : ProjectiveCarrier n → N) (s : Set (ProjectiveCarrier n))
    (hf : letI := a.quotientCharts
      ContMDiffOn 𝓘(ℝ, RModel q) J ∞ f s) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ContMDiffOn 𝓘(ℝ, EModel q) J ∞ f s := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  have hEuclidean : ContMDiffOn (euclideanModel q) J ∞ f s := by
    have h := hf.comp (euclideanModelDiffeomorph n d e q g a).symm.contMDiff.contMDiffOn
      (by intro x hx; exact hx)
    simpa [Function.comp_def, euclideanModelDiffeomorph] using h
  have hSelf : ContMDiffOn 𝓘(ℝ, EModel q) J ∞ f s := by
    have h := hEuclidean.comp
      (euclideanChartDiffeomorph n d e q g a).symm.contMDiff.contMDiffOn
      (by intro x hx; exact hx)
    simpa [Function.comp_def, euclideanChartDiffeomorph] using h
  exact (contMDiffOn_restrictedCharts_iff
    (I := 𝓘(ℝ, EModel q))
    (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    f s).2 hSelf

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeSmoothTransport
