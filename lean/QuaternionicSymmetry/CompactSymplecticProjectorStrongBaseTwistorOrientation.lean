import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorCoordinateLinear
import QuaternionicSymmetry.FourDimensionalHalfSpinConnectionHopfMatch
import QuaternionicSymmetry.ManifoldQuaternionicIsometryOrientation

/-! The actual base twistor coordinate change preserves the oriented
quaternionic cross product. The source commutator is computed in the
concrete quaternion action, and the target commutator in the genuine
descended tangent quaternionic plane. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorOrientation

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorStrongBaseOperatorContinuous
open CompactSymplecticProjectorStrongBaseTwistorCoordinateLinear
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicIntrinsicFiberHomeomorph
open ManifoldQuaternionicIsometryOrientation
open FourDimensionalHalfSpinConnectionHopfMatch
open QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem preferredBaseCoefficientLinear_operator
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
    let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
    tangentSynth Q (baseCoset n)
      (preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn v) =
      strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn v := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let L := tangentSynthLinearEquiv Q (baseCoset n)
  have h := congrArg Subtype.val
    (L.apply_symm_apply (⟨strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn v,
      strongBaseOperatorLinear_mem_plane hLee hDesc hImm n d e q g a hq hn v⟩ :
        ManifoldQuaternionicSpanSymmetry.tangentSpan Q (baseCoset n)))
  exact h

theorem strongBaseOperatorLinear_commutator_cross
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (v w : Fin 3 → ℝ) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn v *
      strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn w -
      strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn w *
        strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn v =
      (2 : ℝ) • strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn
        (crossProduct v w) := by
  letI := a.quotientCharts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  let U := (euclideanModelEquiv q).toLinearEquiv
  let F := baseQuaternionAction hDesc hImm n d e q g a hq
  have hqcomm := congrArg F (pureScalar_cross v w)
  rw [map_sub, map_mul, map_mul] at hqcomm
  have hpure : pureScalar ((2 : ℝ) • crossProduct v w) =
      (2 : ℝ) • pureScalar (crossProduct v w) :=
    (pureScalarLinear.map_smul (2 : ℝ) (crossProduct v w))
  rw [hpure, map_smul] at hqcomm
  ext x
  have hx := congrArg (fun T : Module.End ℝ _ => U (T (U.symm x))) hqcomm
  change U (F (pureScalar v) (F (pureScalar w) (U.symm x))) -
      U (F (pureScalar w) (F (pureScalar v) (U.symm x))) =
    (2 : ℝ) • U (F (pureScalar (crossProduct v w)) (U.symm x))
  simpa only [map_sub, map_smul] using hx.symm

/-- The preferred-coordinate change is orientation-preserving: its source
and target are both the same concrete quaternionic commutator algebra. -/
theorem preferredBaseCoefficientLinear_cross
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (v w : Fin 3 → ℝ) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn
      (crossProduct v w) =
      crossProduct
        (preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn v)
        (preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn w) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let P := preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn
  apply tangentSynth_injective Q (baseCoset n)
  have hs := strongBaseOperatorLinear_commutator_cross hLee hDesc hImm
    n d e q g a hq hn v w
  rw [← preferredBaseCoefficientLinear_operator hLee hDesc hImm
      n d e q g a hq hn v,
    ← preferredBaseCoefficientLinear_operator hLee hDesc hImm
      n d e q g a hq hn w,
    ← preferredBaseCoefficientLinear_operator hLee hDesc hImm
      n d e q g a hq hn (crossProduct v w)] at hs
  have hc : (2 : ℝ) • tangentSynth Q (baseCoset n) (P (crossProduct v w)) =
      (2 : ℝ) • tangentSynth Q (baseCoset n)
        (crossProduct (P v) (P w)) :=
    hs.symm.trans (tangentSynth_commutator_cross Q (baseCoset n) (P v) (P w))
  exact (smul_right_injective
    (TangentSpace 𝓘(ℝ, EModel q) (baseCoset n) →L[ℝ]
      TangentSpace 𝓘(ℝ, EModel q) (baseCoset n))
    (by norm_num : (2 : ℝ) ≠ 0)) hc

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorOrientation
