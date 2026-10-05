import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeDerivativeFrame
import QuaternionicSymmetry.CompactSymplecticProjectorLocalDerivativeCoordinateFormula
import QuaternionicSymmetry.CompactSymplecticProjectorCosetActionBase

/-! The selected smooth Euclidean frame is the genuine translation
differential at the base projector, expressed in the fixed strong chart.
The target-chart change is explicit, so no metric or Q-compatibility is
silently assumed. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeDerivativeCoordinate

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorActualSmoothSectionFrame
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeDerivativeFrame
open CompactSymplecticProjectorLocalDerivativeCoordinateFormula
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorCosetActionBase
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem selected_gaugeDerivativeCoordinates_eq_charted_translation
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
    gaugeDerivativeCoordinates n d e q g a σ x y =
      (tangentCoordChange 𝓘(ℝ, RModel q) y x y).comp
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (σ y)) (baseCoset n)) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
  have hSpec := Classical.choose_spec ((Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.2)
  have hOverlap := hSpec.2.2.1 y hy.2
  have h := gaugeDerivativeCoordinates_eq_coordChange_comp n d e q g a σ x y hOverlap
  have hx : leftCosetAction n (σ x) (baseCoset n) = x := by
    rw [leftCosetAction_baseCoset]
    exact strongGaugeSection_right_inverse hLee hDesc hImm n d e q g a hq hn x x
      (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x)
  have hy' : leftCosetAction n (σ y) (baseCoset n) = y := by
    rw [leftCosetAction_baseCoset]
    exact strongGaugeSection_right_inverse hLee hDesc hImm n d e q g a hq hn x y hy
  simpa only [hx, hy'] using h

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeDerivativeCoordinate
