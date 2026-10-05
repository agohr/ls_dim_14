import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorCoordinateFormula
import QuaternionicSymmetry.ManifoldTwistorCoefficientSphere

/-! The actual base-fiber preferred-coordinate rotation is a smooth map of
the geometric two-sphere, because its concrete tangent-operator formula is
the restriction of a real linear map preserving that sphere. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorSphereSmooth

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseTwistorFiber
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongBaseTwistorCoordinateLinear
open CompactSymplecticProjectorStrongBaseTwistorCoordinateFormula
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def preferredBaseGeometricLinear
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    EuclideanThree →ₗ[ℝ] EuclideanThree := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap.comp
    ((preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn).comp
      (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap)

theorem preferredBaseGeometricLinear_mem_sphere
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (p : geometricSphere) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    preferredBaseGeometricLinear hLee hDesc hImm n d e q g a hq hn p.1 ∈
      Metric.sphere (0 : EuclideanThree) 1 := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let z := coefficientSphereHomeomorph.symm p
  have h := preferredBaseCoefficientLinear_apply hLee hDesc hImm n d e q g a hq hn z
  have hunit : squareNorm
      (preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn z.1) = 1 := by
    rw [h]
    exact ((ManifoldQuaternionicIntrinsicTwistorComparison.preferredFiberEquiv
      (CompactSymplecticProjectorStrongQuaternionicHermitianTangent.strongQuaternionicHermitianTangent
        hLee hDesc hImm n d e q g a hq hn) (baseCoset n)).symm
        (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z)).2
  change toEuclidean
    (preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn z.1) ∈ _
  exact (mem_geometricSphere _).2 hunit

def preferredBaseGeometricSphereMap
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    geometricSphere → geometricSphere := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact fun p => ⟨preferredBaseGeometricLinear hLee hDesc hImm n d e q g a hq hn p.1,
    preferredBaseGeometricLinear_mem_sphere hLee hDesc hImm n d e q g a hq hn p⟩

theorem preferredBaseGeometricSphereMap_smooth
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ContMDiff (𝓡 2) (𝓡 2) ∞
      (preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let L := preferredBaseGeometricLinear hLee hDesc hImm n d e q g a hq hn
  have hs : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanThree) ∞
      (fun p : geometricSphere => L p.1) :=
    L.toContinuousLinearMap.contMDiff.comp contMDiff_coe_sphere
  exact hs.codRestrict_sphere (preferredBaseGeometricLinear_mem_sphere
    hLee hDesc hImm n d e q g a hq hn)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorSphereSmooth
