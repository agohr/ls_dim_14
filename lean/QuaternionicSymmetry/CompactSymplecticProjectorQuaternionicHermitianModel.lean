import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicHermitianTangent
import QuaternionicSymmetry.CompactSymplecticProjectorRiemannianMetric

/-! A source-only actual smooth quaternionic Hermitian projector model.
The selected atlas and metric come from the general registered Lee/Knapp
inputs; no model-specific quaternionic geometry is assumed. Parallelism,
positive curvature, and twistor matching remain separate obligations. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicHermitianModel

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicMetric
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def FirstProjectorModel.quaternionicHermitianTangent
    (m : ℕ)
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (M : FirstProjectorModel m) :
    letI := M.quotientAtlas.quotientCharts
    letI := M.quotientAtlas.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm (m + 1) M.d M.e M.q
      M.groupAtlas M.quotientAtlas M.realDimension (by omega)
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm
      (m + 1) M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension (by omega)
    SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ, EModel M.q)) (M := ProjectiveCarrier (m + 1)) (n := ∞) :=
  strongQuaternionicHermitianTangent hLee hDesc hImm (m + 1) M.d M.e M.q
    M.groupAtlas M.quotientAtlas M.realDimension (by omega)

theorem exists_firstProjectorQuaternionicHermitianModel
    (hClosed : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (hQuot : GeneralLieHomogeneousSpaceSource.LeeHomogeneousSpaceTheorem)
    (hKnapp : CompactSymplecticKnappDimensionSource.KnappCompactSymplecticMatrixDimension)
    (hDim : ManifoldDimensionTopologySource.LeeInvarianceOfDimension)
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (m : ℕ) :
    ∃ M : FirstProjectorModel m,
      letI := M.quotientAtlas.quotientCharts
      letI := M.quotientAtlas.quotientManifold
      letI := strongEuclideanQuotientCharts hLee hDesc hImm (m + 1) M.d M.e M.q
        M.groupAtlas M.quotientAtlas M.realDimension (by omega)
      letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm
        (m + 1) M.d M.e M.q M.groupAtlas M.quotientAtlas M.realDimension (by omega)
      Nonempty (SmoothQuaternionicHermitianTangent
        (I := 𝓘(ℝ, EModel M.q)) (M := ProjectiveCarrier (m + 1)) (n := ∞)) := by
  obtain ⟨M⟩ := exists_firstProjectorModel hClosed hQuot hKnapp hDim m
  exact ⟨M, ⟨FirstProjectorModel.quaternionicHermitianTangent m hLee hDesc hImm M⟩⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicHermitianModel
