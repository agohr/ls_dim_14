import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartCenter
import QuaternionicSymmetry.ManifoldQuaternionicReduction

/-! The selected smooth action-derived frames define a genuine smooth
gauge of the tangent core of the actual strong Euclidean quotient atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentFrameGauge

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeChartCenter
open CompactSymplecticProjectorStrongOrthonormalCoordinateFrame
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicReduction
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def strongTangentFrameGauge
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    TangentFrameGauge 𝓘(ℝ, EModel q)
      (M := ProjectiveCarrier n) (n := ∞) := by
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
  let x (i : atlas (EModel q) (ProjectiveCarrier n)) :=
    strongChartCenter hLee hDesc hImm n d e q g a hq hn i
  refine {
    toFrame := fun i y =>
      localOrthonormalToFrame hLee hDesc hImm n d e q g a hq hn (x i) y
    fromFrame := fun i y =>
      localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn (x i) y
    to_from := ?_
    from_to := ?_
    smooth_to := ?_
    smooth_from := ?_ }
  · intro i y hy v
    have hW : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn (x i) := by
      apply mem_strongGaugeNeighborhood_of_chart_source
        hLee hDesc hImm n d e q g a hq hn i y
      exact hy
    have hPair := (localOrthonormalFrames_inverse
      hLee hDesc hImm n d e q g a hq hn (x i) y hW).1
    exact congrArg (fun L : EModel q →L[ℝ] EModel q => L v) hPair
  · intro i y hy v
    have hW : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn (x i) := by
      apply mem_strongGaugeNeighborhood_of_chart_source
        hLee hDesc hImm n d e q g a hq hn i y
      exact hy
    have hPair := (localOrthonormalFrames_inverse
      hLee hDesc hImm n d e q g a hq hn (x i) y hW).2
    exact congrArg (fun L : EModel q →L[ℝ] EModel q => L v) hPair
  · intro i
    have hSmooth := (localOrthonormalFrames_smooth
      hLee hDesc hImm n d e q g a hq hn (x i)).2
    apply hSmooth.mono
    intro y hy
    exact mem_strongGaugeNeighborhood_of_chart_source
      hLee hDesc hImm n d e q g a hq hn i y hy
  · intro i
    have hSmooth := (localOrthonormalFrames_smooth
      hLee hDesc hImm n d e q g a hq hn (x i)).1
    apply hSmooth.mono
    intro y hy
    exact mem_strongGaugeNeighborhood_of_chart_source
      hLee hDesc hImm n d e q g a hq hn i y hy

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentFrameGauge
