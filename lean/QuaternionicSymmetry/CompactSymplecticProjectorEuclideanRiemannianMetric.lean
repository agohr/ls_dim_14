import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelImmersion
import QuaternionicSymmetry.ManifoldImmersionPullbackMetricGeneral
import QuaternionicSymmetry.FinitePositiveBilinearBounded
import QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric

/-! The actual projector immersion gives a concrete smooth Frobenius-
pullback metric directly on the Euclidean/L² quotient model. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanRiemannianMetric

open Manifold Bundle
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanModelSmoothOrbit
open CompactSymplecticProjectorEuclideanModelImmersion
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def smoothProjectorMetric_euclideanModel
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    letI := euclideanModel_isManifold n d e q g a
    ContMDiffRiemannianMetric (euclideanModel q) ∞ (EModel q)
      (TangentSpace (euclideanModel q) : ProjectiveCarrier n → Type _) := by
  letI := a.quotientCharts
  letI := euclideanModel_isManifold n d e q g a
  exact ManifoldImmersionPullbackMetricGeneral.smoothMetric
    (I := euclideanModel q) (E := EModel q)
    (quotientOrbitProjector n) (frobeniusCLM n)
    (smooth_quotientOrbitProjector_euclideanModel hDesc n d e q g a)
    (quotientOrbitProjector_mfderiv_injective_euclideanModel
      hDesc hImm n d e q g a)
    (frobeniusCLM_symm n) (frobeniusCLM_pos n)
    (FinitePositiveBilinearBounded.unitBall_isVonNBounded
      (frobeniusCLM n) (frobeniusCLM_pos n))

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanRiemannianMetric
