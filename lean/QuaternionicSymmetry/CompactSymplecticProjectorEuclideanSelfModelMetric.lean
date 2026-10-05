import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelOrbit
import QuaternionicSymmetry.ManifoldImmersionPullbackMetricGeneral
import QuaternionicSymmetry.FinitePositiveBilinearBounded
import QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric

/-! Concrete smooth Frobenius-pullback Riemannian metric on the actual
Euclidean-valued quotient atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelMetric

open Manifold Bundle
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanSelfModelOrbit
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def smoothProjectorMetric_selfModel
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := euclideanQuotientCharts n d e q g a
    letI := euclideanQuotientCharts_isManifold n d e q g a
    ContMDiffRiemannianMetric 𝓘(ℝ, EModel q) ∞ (EModel q)
      (TangentSpace 𝓘(ℝ, EModel q) : ProjectiveCarrier n → Type _) := by
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  exact ManifoldImmersionPullbackMetricGeneral.smoothMetric
    (I := 𝓘(ℝ, EModel q)) (E := EModel q)
    (quotientOrbitProjector n) (frobeniusCLM n)
    (smooth_quotientOrbitProjector_selfModel hDesc n d e q g a)
    (quotientOrbitProjector_mfderiv_injective_selfModel
      hDesc hImm n d e q g a)
    (frobeniusCLM_symm n) (frobeniusCLM_pos n)
    (FinitePositiveBilinearBounded.unitBall_isVonNBounded
      (frobeniusCLM n) (frobeniusCLM_pos n))

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelMetric
