import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedNeighborhoodAtlas
import QuaternionicSymmetry.ManifoldChartRefinementDiffeomorph
import QuaternionicSymmetry.ManifoldChartRefinementDifferential

/-! The actual projector immersion remains smooth on the gauge-adapted
Euclidean atlas. Its source chart dictionary is the restricted atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasOrbit

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanSelfModelOrbit
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinementDiffeomorph
open ManifoldChartRefinementDifferential
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem smooth_quotientOrbitProjector_adaptedAtlas
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ContMDiff 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n) ∞
      (quotientOrbitProjector n) := by
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  simpa [ContMDiff, contMDiffAt_iff, extChartAt,
    adaptedEuclideanQuotientCharts, ManifoldChartRefinement.restrictedCharts,
    mfld_simps] using
    (smooth_quotientOrbitProjector_selfModel hDesc n d e q g a)

theorem quotientOrbitProjector_mfderiv_injective_adaptedAtlas
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    Function.Injective
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x) := by
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  let W := actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn
  have hD := mfderiv_restrictedCharts_eq (I := 𝓘(ℝ, EModel q))
    (J := 𝓘(ℝ, Mat n)) W
    (actualGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (quotientOrbitProjector n) x
    ((smooth_quotientOrbitProjector_selfModel hDesc n d e q g a).mdifferentiableAt
      (by simp))
  simpa [W, adaptedEuclideanQuotientCharts] using
    (hD.symm ▸ quotientOrbitProjector_mfderiv_injective_selfModel
      hDesc hImm n d e q g a x)

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasOrbit
