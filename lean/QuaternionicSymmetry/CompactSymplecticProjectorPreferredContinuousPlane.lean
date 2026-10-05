import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicSpanBridge
import QuaternionicSymmetry.CompactSymplecticProjectorQuotientImaginaryPlane

/-! The actual representative-independent projector Q-plane, in the
preferred Euclidean tangent coordinates and continuous-operator carrier
used by the tangent-core transition algebra. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorPreferredContinuousPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorStrongFrameQuaternionicSpanBridge
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def preferredContinuousImaginaryPlane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (y : ProjectiveCarrier n) :
    letI := a.quotientCharts
    Submodule ℝ (EModel q →L[ℝ] EModel q) := by
  letI := a.quotientCharts
  exact ((quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
    (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)).map
    (Module.End.toContinuousLinearMap (𝕜 := ℝ) (EModel q)).toLinearMap

theorem forget_preferredContinuousImaginaryPlane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (y : ProjectiveCarrier n) :
    letI := a.quotientCharts
    Submodule.map (forgetContinuousEnd q)
      (preferredContinuousImaginaryPlane hDesc hImm n d e q g a hq hn y) =
      (quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
        (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
  letI := a.quotientCharts
  ext S
  constructor
  · rintro ⟨T, ⟨S₀, ⟨R, hR, rfl⟩, rfl⟩, rfl⟩
    exact ⟨R, hR, rfl⟩
  · rintro ⟨R, hR, rfl⟩
    exact ⟨Module.End.toContinuousLinearMap (𝕜 := ℝ) (EModel q)
      (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ) R),
      ⟨((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ) R,
        ⟨R, hR, rfl⟩, rfl⟩, rfl⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorPreferredContinuousPlane
