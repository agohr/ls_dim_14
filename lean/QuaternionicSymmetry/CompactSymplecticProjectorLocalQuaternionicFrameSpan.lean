import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicOperatorImage

/-! The local smooth coordinate conjugates of actual I/J/K span
exactly the image of the checked base quaternionic tangent plane. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicFrameSpan

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticProjectorBaseQuaternionicSpan
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorLocalQuaternionicOperatorImage
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def localFrameSpan
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    Submodule ℝ (Module.End ℝ (RModel q)) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  exact Submodule.span ℝ
    ({(localConjugateOperator n d e q g a σ x
        (Module.End.toContinuousLinearMap (RModel q)
          (baseI hDesc hImm n d e q g a hq).toLinearMap) y).toLinearMap,
      (localConjugateOperator n d e q g a σ x
        (Module.End.toContinuousLinearMap (RModel q)
          (baseJ hDesc hImm n d e q g a hq).toLinearMap) y).toLinearMap,
      (localConjugateOperator n d e q g a σ x
        (Module.End.toContinuousLinearMap (RModel q)
          (baseK hDesc hImm n d e q g a hq).toLinearMap) y).toLinearMap} :
      Set (Module.End ℝ (RModel q)))

theorem localFrameSpan_eq_map_baseImaginaryPlane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (σ : ProjectiveCarrier n → G n) (x y : ProjectiveCarrier n) :
    letI := g.charts
    letI := g.manifold
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ E : RModel q ≃L[ℝ] RModel q,
      (E : RModel q →L[ℝ] RModel q) =
        gaugeDerivativeCoordinates n d e q g a σ x y →
      localFrameSpan hDesc hImm n d e q g a hq σ x y =
        (baseImaginaryPlane hDesc hImm n d e q g a hq).map
          ((E.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro E hE
  rw [baseImaginaryPlane_eq_generatorSpan]
  unfold baseGeneratorSpan localFrameSpan
  rw [Submodule.map_span]
  congr 1
  simp [Set.image_insert_eq, localConjugateOperator_toLinearMap n d e q g a σ x y E hE,
    Module.End.toContinuousLinearMap]

end
end QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicFrameSpan
