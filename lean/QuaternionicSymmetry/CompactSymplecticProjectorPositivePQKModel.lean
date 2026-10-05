import QuaternionicSymmetry.CompactSymplecticProjectorStrongScalarPositiveEverywhere
import QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicHermitianModel
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-! The first genuine compact connected positive quaternionic-Kähler
projector model. Its smooth quotient atlas comes from the registered general
Lee/Knapp inputs, its Riemannian metric is the concrete Frobenius pullback,
its compatible Levi-Civita connection is constructed from the ordinary
Petersen theorem, and its scalar positivity is proved by actual matrix
curvature. No model-specific PQK or curvature conclusion is assumed. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorPositivePQKModel

open Manifold Bundle GeneralLeviCivitaSource
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongCompatibleConnection
open CompactSymplecticProjectorStrongScalarPositiveEverywhere
open CompactSymplecticProjectorCarrierConnected
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def FirstProjectorModel.positivePQKGeometry
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
    CompactConnectedPositiveQuaternionicKahlerGeometry
      (E := EModel M.q) (M := ProjectiveCarrier (m + 1)) := by
  letI := M.quotientAtlas.quotientCharts
  letI := M.quotientAtlas.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm (m + 1)
    M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension (Nat.zero_lt_succ m)
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm (m + 1)
    M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension (Nat.zero_lt_succ m)
  letI : ConnectedSpace (ProjectiveCarrier (m + 1)) :=
    projectiveCarrier_connectedSpace (m + 1)
  have hpos : 0 < m + 1 := by omega
  let hExist := actual_positiveScalar_leviCivita_exists
    hPetersen hLee hDesc hImm (m + 1) M.d M.e M.q
      M.groupAtlas M.quotientAtlas M.realDimension hpos
  let D := Classical.choose hExist
  refine {
    tangent := strongQuaternionicHermitianTangent hLee hDesc hImm
      (m + 1) M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension hpos
    connection := actualCompatibleTangentConnection hLee hDesc hImm
      (m + 1) M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension hpos D
    scalar_pos := ?_
    compact := isCompact_univ
    connected := isPreconnected_univ
  }
  intro p y hy
  exact actual_scalarCurvature_pos_on_chart hLee hDesc hImm
    (m + 1) M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension hpos
      D p y hy

theorem exists_actual_positivePQK_firstProjectorModel
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
      Nonempty (CompactConnectedPositiveQuaternionicKahlerGeometry
        (E := EModel M.q) (M := ProjectiveCarrier (m + 1))) := by
  obtain ⟨M⟩ := exists_firstProjectorModel hClosed hQuot hKnapp hDim m
  exact ⟨M, ⟨FirstProjectorModel.positivePQKGeometry
    m hPetersen hLee hDesc hImm M⟩⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorPositivePQKModel
