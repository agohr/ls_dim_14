import QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorSmoothBaseFiber
import QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorFiberFormula

/-! The literal ambient-CP-to-Levi-Civita-twistor map, transported to the
genuine smooth twistor sphere total space, is smooth on the actual base
projective line. The corrected Hopf sign is retained exactly. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorBaseFiberSmooth

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorAmbientActualTwistorFiberFormula
open CompactSymplecticProjectorAmbientActualTwistorEquiv
open CompactSymplecticProjectorAmbientActualTwistorSmoothBaseFiber
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticProjectorStrongTwistorAction
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTwistorSphereManifold
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorCorrectedHopf
open FourDimensionalHalfSpinProjective
open FourDimensionalHalfSpinHopfProjectiveDescent
open FourDimensionalHalfSpinAntipodalVerticalSign
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff LinearAlgebra.Projectivization

noncomputable section
set_option maxHeartbeats 1000000

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem ambientActualTwistor_baseFiber_smoothFormula
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (p : ProjectiveSpinor) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
    (sphereTotalHomeomorph Q).symm
      (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
        (fiberProjectiveLine n (firstColumnSphere n (1 : G n)) p)) =
      strongBaseSmoothTotalFiber hLee hDesc hImm n d e q g a hq hn p := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := strongTwistorAction hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  rw [ambientActualTwistorEquiv_fiber]
  simp only [one_smul]
  have hc : coefficientSphereHomeomorph.symm (correctedHopf p) =
      antipodalCoefficient (projectiveHopf p) := by
    rw [correctedHopf_coefficient]
    exact coefficientSphereHomeomorph.symm_apply_apply _
  rw [← hc, strongBaseTwistorPoint_smoothTotal_formula]
  rfl

/-- The restriction of the SAME concrete ambient projective-to-actual
twistor map to the base projective line is smooth in the independent smooth
twistor-bundle atlas. No smooth structure is transported through the
homeomorphism to obtain this statement. -/
theorem ambientActualTwistor_baseFiber_smooth
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
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ)
      (𝓘(ℝ, EuclideanSpace ℝ (Fin q)).prod (𝓡 2)) ∞
      (fun p : ProjectiveSpinor =>
        (sphereTotalHomeomorph Q).symm
          (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
            (fiberProjectiveLine n (firstColumnSphere n (1 : G n)) p))) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  have heq : (fun p : ProjectiveSpinor =>
      (sphereTotalHomeomorph Q).symm
        (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
          (fiberProjectiveLine n (firstColumnSphere n (1 : G n)) p))) =
      strongBaseSmoothTotalFiber hLee hDesc hImm n d e q g a hq hn := by
    funext p
    exact ambientActualTwistor_baseFiber_smoothFormula hLee hDesc hImm
      n d e q g a hq hn p
  change ContMDiff 𝓘(ℝ, Fin 1 → ℂ)
    (𝓘(ℝ, EuclideanSpace ℝ (Fin q)).prod (𝓡 2)) ∞
    (fun p : ProjectiveSpinor =>
      (sphereTotalHomeomorph Q).symm
        (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
          (fiberProjectiveLine n (firstColumnSphere n (1 : G n)) p)))
  rw [heq]
  exact strongBaseSmoothTotalFiber_smooth hLee hDesc hImm n d e q g a hq hn

end
end QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorBaseFiberSmooth
