import QuaternionicSymmetry.CompactSymplecticProjectorBaseTwistorOperator
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentPlaneIdentification
import QuaternionicSymmetry.CompactSymplecticProjectorOldToStrongTangent

/-! The concrete unit-imaginary base-tangent operator, expressed in the
actual strong Euclidean quotient tangent and its descended Q-plane. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorOperator

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorBaseTwistorOperator
open CompactSymplecticProjectorPreferredContinuousPlane
open CompactSymplecticProjectorStrongTangentPlaneIdentification
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def strongBaseUnitOperator
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n)
    (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    TangentSpace 𝓘(ℝ, EModel q) (baseCoset n) →L[ℝ]
      TangentSpace 𝓘(ℝ, EModel q) (baseCoset n) := by
  letI := a.quotientCharts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  let U := (euclideanModelEquiv q).toLinearEquiv
  let F := baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar z.1)
  exact Module.End.toContinuousLinearMap (𝕜 := ℝ) (EModel q)
    ((U.conjAlgEquiv ℝ) F)

theorem strongBaseUnitOperator_mem_plane
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn z ∈
      ManifoldQuaternionicSpanSymmetry.tangentSpan
        (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
        (baseCoset n) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  rw [tangentSpan_eq_preferredPlane hLee hDesc hImm n d e q g a hq hn]
  change _ ∈ ((CompactSymplecticProjectorQuotientImaginaryPlane.quotientImaginaryPlane
      hDesc hImm n d e q g a hq hn (baseCoset n)).map
        (((euclideanModelEquiv q).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)).map
      (Module.End.toContinuousLinearMap (𝕜 := ℝ) (EModel q)).toLinearMap
  apply Submodule.mem_map.mpr
  refine ⟨_, ?_, rfl⟩
  apply Submodule.mem_map.mpr
  exact ⟨_, base_unit_operator_mem_plane hDesc hImm n d e q g a hq hn z, rfl⟩

theorem strongBaseUnitOperator_square
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ∀ v : TangentSpace 𝓘(ℝ, EModel q) (baseCoset n),
      strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn z
        (strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn z v) = -v := by
  letI := a.quotientCharts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  intro v
  let U := (euclideanModelEquiv q).toLinearEquiv
  let F := baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar z.1)
  have hs := base_unit_operator_square hDesc hImm n d e q g a hq z (U.symm v)
  change U (F (F (U.symm v))) = -v
  rw [hs, map_neg, U.apply_symm_apply]

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorOperator
