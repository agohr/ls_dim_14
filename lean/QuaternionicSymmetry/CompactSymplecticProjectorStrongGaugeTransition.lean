import QuaternionicSymmetry.ManifoldChartRefinementTangentTransition
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartTransition
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeAtlas

/-! Tangent-core transitions in the smooth-section Euclidean atlas are
exactly the canonical conjugates of original quotient chart changes. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeTransition

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanChartTransition
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinement
open ManifoldChartRefinementTangentTransition
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem strong_tangentCoordChange_eq_original_conj
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y z : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI : IsManifold 𝓘(ℝ, RModel q) 1 (ProjectiveCarrier n) :=
      a.quotientManifold.of_le (by norm_cast)
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
      (strongEuclideanQuotientCharts_isManifold
        hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
    tangentCoordChange 𝓘(ℝ, EModel q) x y z =
      (euclideanModelEquiv q).toContinuousLinearMap.comp
        ((tangentCoordChange 𝓘(ℝ, RModel q) x y z).comp
          (euclideanModelEquiv q).symm.toContinuousLinearMap) := by
  letI := a.quotientCharts
  letI : IsManifold 𝓘(ℝ, RModel q) 1 (ProjectiveCarrier n) :=
    a.quotientManifold.of_le (by norm_cast)
  letI := euclideanQuotientCharts n d e q g a
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (euclideanQuotientCharts_isManifold n d e q g a).of_le (by norm_cast)
  let W := strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn
  have hNew := restrictedCharts_isManifold (I := 𝓘(ℝ, EModel q))
    (n := 1) W
    (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
  have hRestr := tangentCoordChange_restrictedCharts_eq
    (I := 𝓘(ℝ, EModel q)) W
    (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    hNew x y z
  have hModel := selfModel_tangentCoordChange_eq_original_conj
    n d e q g a x y z
  exact hRestr.trans hModel

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeTransition
