import QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorBaseFiberComplex
import QuaternionicSymmetry.CompactSymplecticProjectorStrongCompatibleExistence

/-! Source-only actual-model base-fiber conclusion: Petersen supplies only an
ordinary Levi-Civita connection, while the model's quaternionic preservation,
actual map smoothness and vertical complex compatibility are proved internally. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorBaseFiberSource

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongCompatibleExistence
open CompactSymplecticProjectorAmbientActualTwistorEquiv
open CompactSymplecticProjectorAmbientActualTwistorBaseFiberSmooth
open CompactSymplecticProjectorAmbientActualTwistorBaseFiberComplex
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open GeneralLeviCivitaSource
open ManifoldTwistorSphereManifold
open ManifoldTwistorGlobalAlmostComplex
open FourDimensionalHalfSpinProjective
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev J (q : ℕ) := (𝓘(ℝ, EModel q)).prod (𝓡 2)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem actual_ambient_baseFiber_smooth_complex_exists
    (hPetersen : PetersenLeviCivitaExistenceTheorem.{0, 0})
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
    let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
    ∃ D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q,
      ContMDiff 𝓘(ℝ, Fin 1 → ℂ) (J q) ∞
        (fun p : ProjectiveSpinor =>
          (sphereTotalHomeomorph Q).symm
            (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
              (fiberProjectiveLine n (firstColumnSphere n (1 : G n)) p))) ∧
      ∀ (p : ProjectiveSpinor) (v : Fin 1 → ℂ),
        mfderiv 𝓘(ℝ, Fin 1 → ℂ) (J q)
          (fun s : ProjectiveSpinor =>
            (sphereTotalHomeomorph Q).symm
              (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
                (fiberProjectiveLine n (firstColumnSphere n (1 : G n)) s)))
          p (Complex.I • v) =
          tangentComplex Q D
            ((sphereTotalHomeomorph Q).symm
              (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
                (fiberProjectiveLine n (firstColumnSphere n (1 : G n)) p)))
            (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (J q)
              (fun s : ProjectiveSpinor =>
                (sphereTotalHomeomorph Q).symm
                  (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
                    (fiberProjectiveLine n (firstColumnSphere n (1 : G n)) s))) p v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  obtain ⟨D⟩ := actual_compatible_tangent_connection_exists
    hPetersen hLee hDesc hImm n d e q g a hq hn
  refine ⟨D, ?_, ?_⟩
  · exact ambientActualTwistor_baseFiber_smooth hLee hDesc hImm
      n d e q g a hq hn
  · intro p v
    exact ambientActualTwistor_baseFiber_mfderiv_complex hLee hDesc hImm
      n d e q g a hq hn D p v

end
end QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorBaseFiberSource
