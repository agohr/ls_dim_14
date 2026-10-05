import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelTangentFormula

/-! The smooth Euclidean gauge is exactly the conjugate of the original
genuine tangent-coordinate gauge by the differential of the model change. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanGaugeTangentIdentification

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanQuaternionicPlane
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorAdaptedAtlasEuclideanGauge
open CompactSymplecticProjectorEuclideanModelTangentFormula
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem euclideanLocalConjugateOperator_eq_tangentConjugate
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n)
    (S : RModel q →L[ℝ] RModel q) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts
      n d e q g a
    (euclideanLocalConjugateOperator n d e q g a σ x S y).toLinearMap =
      (((euclideanTangentEquiv n d e q g a y).trans
        (CompactSymplecticProjectorEuclideanSelfModelPlane.selfModelTangentEquiv
          n d e q g a y)).toLinearEquiv.conjAlgEquiv ℝ)
        (localConjugateOperator n d e q g a σ x S y).toLinearMap := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts n d e q g a
  rw [originalToSelf_tangentEquiv_eq_coordinateEquiv n d e q g a y]
  ext v
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanGaugeTangentIdentification
