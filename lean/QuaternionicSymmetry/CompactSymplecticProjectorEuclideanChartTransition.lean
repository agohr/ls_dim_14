import QuaternionicSymmetry.ManifoldTangentCoordinateModelChange
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridge

/-! The genuine Euclidean quotient chart transition is the conjugate of
the original quotient chart transition by the canonical linear equivalence. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartTransition

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanChartBridge
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open ManifoldTangentCoordinateModelChange
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem selfModel_tangentCoordChange_eq_original_conj
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x y z : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI : IsManifold 𝓘(ℝ, RModel q) 1 (ProjectiveCarrier n) :=
      a.quotientManifold.of_le (by norm_cast)
    letI := euclideanQuotientCharts n d e q g a
    letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
      (euclideanQuotientCharts_isManifold n d e q g a).of_le
        (by norm_cast)
    tangentCoordChange 𝓘(ℝ, EModel q) x y z =
      (euclideanModelEquiv q).toContinuousLinearMap.comp
        ((tangentCoordChange 𝓘(ℝ, RModel q) x y z).comp
          (euclideanModelEquiv q).symm.toContinuousLinearMap) := by
  letI := a.quotientCharts
  letI : IsManifold 𝓘(ℝ, RModel q) 1 (ProjectiveCarrier n) :=
    a.quotientManifold.of_le (by norm_cast)
  letI := euclideanQuotientCharts n d e q g a
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (euclideanQuotientCharts_isManifold n d e q g a).of_le
      (by norm_cast)
  change fderivWithin ℝ
    ((extChartAt 𝓘(ℝ, EModel q) y) ∘
      (extChartAt 𝓘(ℝ, EModel q) x).symm)
    (Set.range 𝓘(ℝ, EModel q))
    ((extChartAt 𝓘(ℝ, EModel q) x) z) = _
  rw [← euclideanQuotient_extendedChart_eq n d e q g a x,
    ← euclideanQuotient_extendedChart_eq n d e q g a y]
  simpa [euclideanModel, ModelWithCorners.transContinuousLinearEquiv_range,
    modelWithCornersSelf_coe] using
    (tangentCoordChange_transContinuousLinearEquiv
      (euclideanModelEquiv q) x y z)

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartTransition
