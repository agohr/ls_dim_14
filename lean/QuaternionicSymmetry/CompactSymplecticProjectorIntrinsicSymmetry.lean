import QuaternionicSymmetry.CompactSymplecticProjectorPositivePQKModel
import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicPointIsometry
import QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryDerivative
import QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry

/-! A concrete regression for the intrinsic Stage 2 endpoint. The existing
projector reflections are assembled into actual global point symmetries of
the very metric in the constructed positive PQK geometry. No classification,
twistor recognition, or model-specific symmetry source is assumed here.

This example does not instantiate the Picard-generator branch of contact
recognition, and does not assert consistency of every literature premise. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorIntrinsicSymmetry

open Manifold
open ManifoldRiemannianIntrinsicSymmetry
open ManifoldPositiveQuaternionicKahlerGeometry
open GeneralLeviCivitaSource GeneralSmoothLocalSectionSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongQuaternionicPointIsometry
open CompactSymplecticProjectorStrongPointSymmetry
open CompactSymplecticProjectorStrongPointSymmetryDerivative
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticProjectorPositivePQKModel
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

/-- The checked matrix reflection, with scale one and derivative `-id`,
inhabits the same point-symmetry type used by the classification endpoint. -/
def actualPointSymmetry
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    PointSymmetry
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn) x := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  refine {
    map := {
      map := strongPointSymmetryDiffeomorph hLee hDesc hImm n d e q g a hq hn x
      scale := 1
      scale_pos := zero_lt_one
      metric_eq := ?_
    }
    scale_one := rfl
    fixed := ?_
    deriv_neg := ?_
  }
  · intro y v w
    simpa only [one_mul] using
      (pointSymmetry_is_quaternionic_isometry hLee hDesc hImm
        n d e q g a hq hn x).1 y v w
  · exact pointSymmetry_fixed n x
  · intro v
    exact pointSymmetry_mfderiv_neg_strong hLee hDesc hImm n d e q g a hq hn x v

/-- Intrinsic symmetry of the actual positive metric, not a separate model flag. -/
theorem FirstProjectorModel.positivePQKGeometry_isRiemannianSymmetric
    (m : ℕ)
    (hPetersen : PetersenLeviCivitaExistenceTheorem.{0, 0})
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (M : FirstProjectorModel m) :
    letI := M.quotientAtlas.quotientCharts
    letI := M.quotientAtlas.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm (m + 1)
      M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension (Nat.zero_lt_succ m)
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm (m + 1)
      M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension (Nat.zero_lt_succ m)
    IsRiemannianSymmetric
      (FirstProjectorModel.positivePQKGeometry m hPetersen hLee hDesc hImm M).tangent := by
  letI := M.quotientAtlas.quotientCharts
  letI := M.quotientAtlas.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm (m + 1)
    M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension (Nat.zero_lt_succ m)
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm (m + 1)
    M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension (Nat.zero_lt_succ m)
  intro x
  exact ⟨actualPointSymmetry hLee hDesc hImm (m + 1) M.d M.e M.q
    M.groupAtlas M.quotientAtlas M.realDimension (Nat.zero_lt_succ m) x⟩

/-- Source-relative non-vacuity: the actual PQK hypotheses and intrinsic
symmetry hold together on a constructed nonempty projector manifold. -/
theorem exists_actual_positivePQK_intrinsicSymmetric_model
    (hClosed : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (hQuot : GeneralLieHomogeneousSpaceSource.LeeHomogeneousSpaceTheorem)
    (hKnapp : CompactSymplecticKnappDimensionSource.KnappCompactSymplecticMatrixDimension)
    (hDim : ManifoldDimensionTopologySource.LeeInvarianceOfDimension)
    (hPetersen : PetersenLeviCivitaExistenceTheorem.{0, 0})
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (m : ℕ) :
    ∃ M : FirstProjectorModel m,
      letI := M.quotientAtlas.quotientCharts
      letI := M.quotientAtlas.quotientManifold
      letI := strongEuclideanQuotientCharts hLee hDesc hImm (m + 1)
        M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension (Nat.zero_lt_succ m)
      letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm (m + 1)
        M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension (Nat.zero_lt_succ m)
      Nonempty (ProjectiveCarrier (m + 1)) ∧
      ∃ P : CompactConnectedPositiveQuaternionicKahlerGeometry
          (E := EModel M.q) (M := ProjectiveCarrier (m + 1)),
        IsRiemannianSymmetric P.tangent := by
  obtain ⟨M⟩ := exists_firstProjectorModel hClosed hQuot hKnapp hDim m
  refine ⟨M, inferInstance, FirstProjectorModel.positivePQKGeometry
    m hPetersen hLee hDesc hImm M, ?_⟩
  exact FirstProjectorModel.positivePQKGeometry_isRiemannianSymmetric
    m hPetersen hLee hDesc hImm M

end
end QuaternionicSymmetry.CompactSymplecticProjectorIntrinsicSymmetry
