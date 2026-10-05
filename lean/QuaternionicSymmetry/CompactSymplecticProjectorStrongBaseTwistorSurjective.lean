import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorInjective
import QuaternionicSymmetry.CompactSymplecticProjectorImaginaryUnitCoordinates
import QuaternionicSymmetry.CompactSymplecticProjectorStabilizerTransport
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentPlaneIdentification

/-! Every intrinsic complex structure in the actual Levi-Civita Q-plane
over the base projector comes from a unique imaginary unit quaternion. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorSurjective

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticProjectorBaseImaginaryRank
open CompactSymplecticProjectorStabilizerTransport
open CompactSymplecticProjectorTranslatedImaginaryPlane
open CompactSymplecticProjectorStrongBaseTwistorOperator
open CompactSymplecticProjectorStrongBaseTwistorFiber
open CompactSymplecticProjectorStrongTangentPlaneIdentification
open CompactSymplecticProjectorPreferredContinuousPlane
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorImaginaryUnitCoordinates
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicDerivativeAction
open ManifoldTwistorSphereBundle
open QuaternionicUnitScalarIsometries
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem strongBaseIntrinsicFiberPoint_surjective
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
    Function.Surjective
      (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro B
  let U := (euclideanModelEquiv q).toLinearEquiv
  let P := CompactSymplecticProjectorQuotientImaginaryPlane.quotientImaginaryPlane
    hDesc hImm n d e q g a hq hn (baseCoset n)
  have hP : P = baseImaginaryPlane hDesc hImm n d e q g a hq := by
    change translatedImaginaryPlane hDesc hImm n d e q g a hq
      (1 : firstPairStabilizer n).1 = _
    exact translatedImaginaryPlane_stabilizer hDesc hImm n d e q g a hq hn 1
  have hmem : B.1.1 ∈ preferredContinuousImaginaryPlane
      hDesc hImm n d e q g a hq hn (baseCoset n) := by
    rw [← tangentSpan_eq_preferredPlane hLee hDesc hImm n d e q g a hq hn]
    exact B.1.2
  change B.1.1 ∈ (P.map (U.conjAlgEquiv ℝ).toLinearMap).map
    (Module.End.toContinuousLinearMap (𝕜 := ℝ) (EModel q)).toLinearMap at hmem
  obtain ⟨S, hS, hSB⟩ := Submodule.mem_map.mp hmem
  obtain ⟨T, hT, hTS⟩ := Submodule.mem_map.mp hS
  rw [hP] at hT
  obtain ⟨r, hr, hTr⟩ := Submodule.mem_map.mp hT
  have hr0 : r.re = 0 := LinearMap.mem_ker.mp hr
  let F := baseQuaternionAction hDesc hImm n d e q g a hq
  have hBv (v : RModel q) : B.1.1 (U v) = U (F r v) := by
    rw [← hSB, ← hTS, ← hTr]
    rfl
  have hrSquareAction : F (r * r) = F (-1 : ℍ) := by
    ext v
    apply U.injective
    calc
      U (F (r * r) v) = U (F r (F r v)) := by rw [map_mul]; rfl
      _ = B.1.1 (B.1.1 (U v)) := by rw [hBv, hBv]
      _ = -U v := B.2 (U v)
      _ = U (F (-1 : ℍ) v) := by simp [F]
  have hrsq : r * r = -1 :=
    (baseQuaternionAction_injective hDesc hImm n d e q g a hq hn) hrSquareAction
  obtain ⟨z, hz⟩ := exists_unit_coordinates r hr0 hrsq
  refine ⟨z, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  ext v
  change U (F (pureScalar z.1) (U.symm v)) = B.1.1 v
  rw [hz]
  simpa only [U.apply_symm_apply] using (hBv (U.symm v)).symm

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorSurjective
