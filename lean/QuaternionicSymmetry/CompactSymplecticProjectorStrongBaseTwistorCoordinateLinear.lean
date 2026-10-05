import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPreferredCoordinate
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseOperatorContinuous
import QuaternionicSymmetry.ManifoldQuaternionicIntrinsicFiberHomeomorph

/-! The preferred-coordinate change at the actual base twistor fiber is
induced by one real linear map on all imaginary-quaternion coefficients. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorCoordinateLinear

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseTwistorOperator
open CompactSymplecticProjectorStrongBaseOperatorContinuous
open CompactSymplecticProjectorStrongBaseTwistorFiber
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicIntrinsicFiberHomeomorph
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

private def basisSphere (t : Fin 3) : coefficientSphere :=
  ⟨Pi.basisFun ℝ (Fin 3) t, by
    fin_cases t <;> simp [squareNorm, Pi.basisFun_apply, Pi.single_apply,
      Fin.sum_univ_succ]⟩

theorem strongBaseOperatorLinear_mem_plane
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (v : Fin 3 → ℝ) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn v ∈
      ManifoldQuaternionicSpanSymmetry.tangentSpan
        (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
        (baseCoset n) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let L := strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn
  have hb (t : Fin 3) : L (Pi.basisFun ℝ (Fin 3) t) ∈
      ManifoldQuaternionicSpanSymmetry.tangentSpan Q (baseCoset n) := by
    simpa only [basisSphere, strongBaseOperatorLinear_apply] using
      strongBaseUnitOperator_mem_plane hLee hDesc hImm n d e q g a hq hn
        (basisSphere t)
  have hv : v = ∑ t : Fin 3, v t • Pi.basisFun ℝ (Fin 3) t := by
    simpa [Pi.basisFun_repr] using ((Pi.basisFun ℝ (Fin 3)).sum_repr v).symm
  rw [hv, map_sum]
  apply Submodule.sum_mem
  intro t _
  simpa only [map_smul] using
    (ManifoldQuaternionicSpanSymmetry.tangentSpan Q (baseCoset n)).smul_mem (v t) (hb t)

def preferredBaseCoefficientLinear
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
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  exact (tangentSynthLinearEquiv Q (baseCoset n)).symm.toLinearMap.comp
    ((strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn).codRestrict
      (ManifoldQuaternionicSpanSymmetry.tangentSpan Q (baseCoset n))
      (strongBaseOperatorLinear_mem_plane hLee hDesc hImm n d e q g a hq hn))

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorCoordinateLinear
