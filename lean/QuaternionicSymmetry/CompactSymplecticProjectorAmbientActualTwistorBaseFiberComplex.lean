import QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorBaseFiberSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorVerticalComplex
import QuaternionicSymmetry.ManifoldTwistorSphereFiberComplex
import QuaternionicSymmetry.CompactSymplecticProjectorBaseStandardQuaternionicStructure

/-! Complex linearity of the literal ambient CP→actual Levi-Civita twistor
map on the base projective fiber, in the independently constructed smooth
twistor atlas and its connection-defined almost-complex tensor. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorBaseFiberComplex

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongBaseTwistorSphereSmooth
open CompactSymplecticProjectorStrongBaseTwistorVerticalComplex
open CompactSymplecticProjectorAmbientActualTwistorSmoothBaseFiber
open CompactSymplecticProjectorAmbientActualTwistorBaseFiberSmooth
open CompactSymplecticProjectorAmbientActualTwistorEquiv
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTwistorSphereFiberInclusion
open ManifoldTwistorSphereManifold
open ManifoldTwistorSphereFiberComplex
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereBundle
open ManifoldTwistorVerticalComplex
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorLocalAlmostComplex
open ManifoldTwistorCorrectedHopf
open FourDimensionalHalfSpinProjective
open FourDimensionalHalfSpinHopfProjectiveDescent
open FourDimensionalHalfSpinAntipodalVerticalSign
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev J (q : ℕ) := (𝓘(ℝ, EModel q)).prod (𝓡 2)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem rotatedCorrectedHopf_mfderiv_complex
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (p : ProjectiveSpinor) (v : Fin 1 → ℂ) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    let f := preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
    let z := antipodalCoefficient (projectiveHopf p)
    let b := coefficientSphereHomeomorph.symm (f (coefficientSphereHomeomorph z))
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) (f ∘ correctedHopf) p (Complex.I • v) =
      sphereVerticalComplex b
        (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) (f ∘ correctedHopf) p v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let f := preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
  let z := antipodalCoefficient (projectiveHopf p)
  let b := coefficientSphereHomeomorph.symm (f (coefficientSphereHomeomorph z))
  have hf : MDifferentiableAt (𝓡 2) (𝓡 2) f (correctedHopf p) :=
    (preferredBaseGeometricSphereMap_smooth hLee hDesc hImm n d e q g a hq hn)
      |>.mdifferentiableAt (by simp)
  have hc : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) correctedHopf p :=
    correctedHopf_smooth.mdifferentiableAt (by simp)
  rw [show correctedHopf p = coefficientSphereHomeomorph z from
    correctedHopf_coefficient p] at hf
  change mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) (f ∘ correctedHopf) p
      (Complex.I • v) =
    sphereVerticalComplex b
      (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) (f ∘ correctedHopf) p v)
  rw [mfderiv_comp p hf hc]
  change mfderiv (𝓡 2) (𝓡 2) f (correctedHopf p)
      (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) correctedHopf p (Complex.I • v)) =
    sphereVerticalComplex b
      (mfderiv (𝓡 2) (𝓡 2) f (correctedHopf p)
        (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) correctedHopf p v))
  rw [correctedHopf_mfderiv_complex (standardRealQuaternionicStructure n q hq)]
  exact preferredBaseSphereMap_mfderiv_complex hLee hDesc hImm
    n d e q g a hq hn z _

theorem strongBaseSmoothTotalFiber_mfderiv
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (p : ProjectiveSpinor) (v : Fin 1 → ℂ) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    let f := preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) (J q)
      (strongBaseSmoothTotalFiber hLee hDesc hImm n d e q g a hq hn) p v =
      (0, mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) (f ∘ correctedHopf) p v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
  let φ := f ∘ correctedHopf
  have hφ : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) φ p :=
    ((preferredBaseGeometricSphereMap_smooth hLee hDesc hImm n d e q g a hq hn).comp
      correctedHopf_smooth).mdifferentiableAt (by simp)
  have hi : MDifferentiableAt (𝓡 2) (J q)
      (sphereFiberInclusion Q (baseCoset n)) (φ p) :=
    (sphereFiberInclusion_smooth Q (baseCoset n)).mdifferentiableAt (by simp)
  change mfderiv 𝓘(ℝ, Fin 1 → ℂ) (J q)
      (sphereFiberInclusion Q (baseCoset n) ∘ φ) p v = _
  rw [mfderiv_comp p hi hφ]
  change mfderiv (𝓡 2) (J q) (sphereFiberInclusion Q (baseCoset n)) (φ p)
      (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) φ p v) = _
  exact sphereFiberInclusion_mfderiv Q (baseCoset n) (φ p) _

theorem strongBaseSmoothTotalFiber_mfderiv_complex
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
    ∀ (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
      (p : ProjectiveSpinor) (v : Fin 1 → ℂ),
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) (J q)
      (strongBaseSmoothTotalFiber hLee hDesc hImm n d e q g a hq hn) p
      (Complex.I • v) =
      tangentComplex Q D
        (strongBaseSmoothTotalFiber hLee hDesc hImm n d e q g a hq hn p)
        (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (J q)
          (strongBaseSmoothTotalFiber hLee hDesc hImm n d e q g a hq hn) p v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  intro _ D p v
  let f := preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
  let z := antipodalCoefficient (projectiveHopf p)
  let b := coefficientSphereHomeomorph.symm (f (coefficientSphereHomeomorph z))
  change mfderiv 𝓘(ℝ, Fin 1 → ℂ) (J q)
      (strongBaseSmoothTotalFiber hLee hDesc hImm n d e q g a hq hn) p
      (Complex.I • v) = _
  rw [strongBaseSmoothTotalFiber_mfderiv hLee hDesc hImm n d e q g a hq hn p
      (Complex.I • v),
    strongBaseSmoothTotalFiber_mfderiv hLee hDesc hImm n d e q g a hq hn p v]
  rw [rotatedCorrectedHopf_mfderiv_complex hLee hDesc hImm
    n d e q g a hq hn p v]
  have hb : f (correctedHopf p) = coefficientSphereHomeomorph b := by
    rw [correctedHopf_coefficient]
    exact (coefficientSphereHomeomorph.apply_symm_apply _).symm
  change (0, sphereVerticalComplex b _) =
    tangentComplex Q D (sphereFiberInclusion Q (baseCoset n) (f (correctedHopf p))) (0,_)
  rw [hb]
  exact (tangentComplex_vertical_pair Q D (baseCoset n) b _).symm

/-- The independently defined ambient projective-to-actual-twistor map is
holomorphic on the actual base projective line, at the differential level.
The connection input is the concrete compatible connection already derived
from the model's Levi-Civita connection; no complex conclusion is assumed. -/
theorem ambientActualTwistor_baseFiber_mfderiv_complex
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
    ∀ (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
      (p : ProjectiveSpinor) (v : Fin 1 → ℂ),
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
  intro _ D p v
  have heq : (fun s : ProjectiveSpinor =>
      (sphereTotalHomeomorph Q).symm
        (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
          (fiberProjectiveLine n (firstColumnSphere n (1 : G n)) s))) =
      strongBaseSmoothTotalFiber hLee hDesc hImm n d e q g a hq hn := by
    funext s
    exact ambientActualTwistor_baseFiber_smoothFormula hLee hDesc hImm
      n d e q g a hq hn s
  change mfderiv 𝓘(ℝ, Fin 1 → ℂ) (J q)
      (fun s : ProjectiveSpinor =>
        (sphereTotalHomeomorph Q).symm
          (ambientActualTwistorEquiv hLee hDesc hImm n d e q g a hq hn
            (fiberProjectiveLine n (firstColumnSphere n (1 : G n)) s)))
      p (Complex.I • v) = _
  rw [heq]
  rw [ambientActualTwistor_baseFiber_smoothFormula hLee hDesc hImm
    n d e q g a hq hn p]
  exact strongBaseSmoothTotalFiber_mfderiv_complex hLee hDesc hImm
    n d e q g a hq hn D p v

end
end QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorBaseFiberComplex
