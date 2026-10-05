import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedNeighborhoodAtlas
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridge
import QuaternionicSymmetry.ManifoldChartRefinementSmoothness

/-! An actual smooth local operator gauge in the original quotient charts
is still smooth after the Euclidean model change and open chart refinement. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasLocalSmooth

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanChartBridge
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinementSmoothness
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem contMDiffOn_adaptedAtlas_of_original
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (f : ProjectiveCarrier n → B) (s : Set (ProjectiveCarrier n))
    (hf : letI := a.quotientCharts
      ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, B) ∞ f s) :
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, B) ∞ f s := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  have hEuclidean : ContMDiffOn (euclideanModel q) 𝓘(ℝ, B) ∞ f s := by
    have h := hf.comp (euclideanModelDiffeomorph n d e q g a).symm.contMDiff.contMDiffOn
      (by intro x hx; exact hx)
    simpa [Function.comp_def, euclideanModelDiffeomorph] using h
  have hSelf : ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, B) ∞ f s := by
    have h := hEuclidean.comp
      (euclideanChartDiffeomorph n d e q g a).symm.contMDiff.contMDiffOn
      (by intro x hx; exact hx)
    simpa [Function.comp_def, euclideanChartDiffeomorph] using h
  exact (contMDiffOn_restrictedCharts_iff
    (I := 𝓘(ℝ, EModel q))
    (actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (actualGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    f s).2 hSelf

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasLocalSmooth
