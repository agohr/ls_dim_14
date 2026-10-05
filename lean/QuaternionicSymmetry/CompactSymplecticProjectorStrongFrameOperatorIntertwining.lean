import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricCompatibility
import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicIntertwining
import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasEuclideanGauge

/-! The same selected invertible action derivative that gives the smooth
metric frame also transports every base-tangent operator intertwined by
the explicit orthonormal base frame. This is a concrete algebraic bridge
to local quaternionic I/J/K, not an assumed Q-reduction. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameOperatorIntertwining

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseOrthonormalCoordinates
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeDerivativeFrame
open CompactSymplecticProjectorStrongOrthonormalCoordinateFrame
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem selectedOperator_intertwines_localFrame
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)
    (S : RModel q →L[ℝ] RModel q) (T : EModel q →L[ℝ] EModel q)
    (hST : ∀ v : EModel q,
      (euclideanModelEquiv q)
        (S (baseOrthonormalFrame hDesc hImm n d e q g a hq v)) =
      (euclideanModelEquiv q)
        (baseOrthonormalFrame hDesc hImm n d e q g a hq (T v))) :
    letI := a.quotientCharts
    ∀ v : EModel q,
      euclideanLocalConjugateOperator n d e q g a
        (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x S y
        (localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y v) =
      localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y (T v) := by
  letI := a.quotientCharts
  intro v
  let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
  have hPair := (selected_derivative_inverse_pair
    hLee hDesc hImm n d e q g a hq hn x y hy).2
  have hCancel (z : EModel q) :
      euclideanGaugeDerivativeInverse n d e q g a σ x y
        (euclideanGaugeDerivative n d e q g a σ x y z) = z := by
    exact congrArg (fun L : EModel q →L[ℝ] EModel q => L z) hPair
  change euclideanGaugeDerivative n d e q g a σ x y
      ((euclideanModelEquiv q)
        (S ((euclideanModelEquiv q).symm
          (euclideanGaugeDerivativeInverse n d e q g a σ x y
            (euclideanGaugeDerivative n d e q g a σ x y
              (baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq v)))))) = _
  rw [hCancel]
  change euclideanGaugeDerivative n d e q g a σ x y
    ((euclideanModelEquiv q)
      (S (baseOrthonormalFrame hDesc hImm n d e q g a hq v))) = _
  rw [hST v]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameOperatorIntertwining
