import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanCharts

/-! Comparison of the equivalent Euclidean model chart and the
genuine Euclidean-valued quotient chart. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridge

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Manifold ContDiff
noncomputable section

private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem euclideanQuotient_extendedChart_eq
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    (letI := a.quotientCharts
     extChartAt (euclideanModel q) x) =
      (letI := euclideanQuotientCharts n d e q g a
       extChartAt 𝓘(ℝ, EModel q) x) := by
  simp only [extChartAt, euclideanModel]
  rw [euclideanQuotientCharts_chartAt]
  apply PartialEquiv.ext
  · intro z
    simp
  · intro z
    simp
  · simp [mfld_simps]

def euclideanChartDiffeomorph
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    letI := euclideanQuotientCharts n d e q g a
    Diffeomorph (euclideanModel q) 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) (ProjectiveCarrier n) ∞ := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  refine ⟨Equiv.refl _, ?_, ?_⟩
  · intro x
    rw [contMDiffAt_iff]
    simpa [euclideanQuotient_extendedChart_eq, euclideanModel,
      ModelWithCorners.transContinuousLinearEquiv_range] using
      (contMDiffAt_iff.mp (contMDiffAt_id (I := euclideanModel q) (x := x)))
  · intro x
    rw [contMDiffAt_iff]
    simpa [← euclideanQuotient_extendedChart_eq, euclideanModel,
      ModelWithCorners.transContinuousLinearEquiv_range] using
      (contMDiffAt_iff.mp (contMDiffAt_id (I := 𝓘(ℝ, EModel q)) (x := x)))

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridge
