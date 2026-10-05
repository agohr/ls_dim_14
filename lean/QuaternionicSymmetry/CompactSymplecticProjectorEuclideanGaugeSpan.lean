import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanGaugeTangentIdentification
import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicFrameSpan

/-! The three smooth Euclidean gauge operators span exactly the
canonical tangent-coordinate transport of the checked original local plane. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanGaugeSpan

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorLocalQuaternionicFrameSpan
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticProjectorEuclideanGaugeTangentIdentification
open CompactSymplecticProjectorEuclideanModelTangentFormula
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def euclideanLocalFrameSpan
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    Submodule ℝ (Module.End ℝ (EModel q)) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  exact Submodule.span ℝ
    ({(euclideanLocalConjugateOperator n d e q g a σ x
        (Module.End.toContinuousLinearMap (RModel q)
          (baseI hDesc hImm n d e q g a hq).toLinearMap) y).toLinearMap,
      (euclideanLocalConjugateOperator n d e q g a σ x
        (Module.End.toContinuousLinearMap (RModel q)
          (baseJ hDesc hImm n d e q g a hq).toLinearMap) y).toLinearMap,
      (euclideanLocalConjugateOperator n d e q g a σ x
        (Module.End.toContinuousLinearMap (RModel q)
          (baseK hDesc hImm n d e q g a hq).toLinearMap) y).toLinearMap} :
      Set (Module.End ℝ (EModel q)))

theorem euclideanLocalFrameSpan_eq_original_map
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    euclideanLocalFrameSpan hDesc hImm n d e q g a hq σ x y =
      (localFrameSpan hDesc hImm n d e q g a hq σ x y).map
        (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  have hS (S : RModel q →L[ℝ] RModel q) :
      (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ)
        (localConjugateOperator n d e q g a σ x S y).toLinearMap) =
        (euclideanLocalConjugateOperator n d e q g a σ x S y).toLinearMap := by
    letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts
      n d e q g a
    simpa [originalToSelf_tangentEquiv_eq_coordinateEquiv n d e q g a y] using
      (euclideanLocalConjugateOperator_eq_tangentConjugate
        n d e q g a σ x y S).symm
  unfold euclideanLocalFrameSpan localFrameSpan
  rw [Submodule.map_span]
  congr 1
  simp [Set.image_insert_eq, hS]

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanGaugeSpan
