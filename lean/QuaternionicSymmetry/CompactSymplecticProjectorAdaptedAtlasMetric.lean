import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasOrbit
import QuaternionicSymmetry.ManifoldImmersionPullbackMetricGeneral
import QuaternionicSymmetry.FinitePositiveBilinearBounded
import QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric

/-! The gauge-adapted Euclidean atlas carries the same concrete
Frobenius-pullback metric, now as a genuine smooth Riemannian tensor. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasMetric

open Manifold Bundle
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedAtlasOrbit
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def smoothProjectorMetric_adaptedAtlas
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := adaptedEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    ContMDiffRiemannianMetric 𝓘(ℝ, EModel q) ∞ (EModel q)
      (TangentSpace 𝓘(ℝ, EModel q) : ProjectiveCarrier n → Type _) := by
  letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := adaptedEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  exact ManifoldImmersionPullbackMetricGeneral.smoothMetric
    (I := 𝓘(ℝ, EModel q)) (E := EModel q)
    (quotientOrbitProjector n) (frobeniusCLM n)
    (smooth_quotientOrbitProjector_adaptedAtlas
      hLee hDesc hImm n d e q g a hq hn)
    (quotientOrbitProjector_mfderiv_injective_adaptedAtlas
      hLee hDesc hImm n d e q g a hq hn)
    (frobeniusCLM_symm n) (frobeniusCLM_pos n)
    (FinitePositiveBilinearBounded.unitBall_isVonNBounded
      (frobeniusCLM n) (frobeniusCLM_pos n))

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasMetric
