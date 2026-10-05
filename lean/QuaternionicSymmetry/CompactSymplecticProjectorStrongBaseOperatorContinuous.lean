import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorOperator

/-! The actual basepoint twistor operator depends linearly, hence
continuously, on its three imaginary quaternion coefficients. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseOperatorContinuous

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongBaseTwistorOperator
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def pureScalarLinear : (Fin 3 → ℝ) →ₗ[ℝ] ℍ where
  toFun := pureScalar
  map_add' a b := by
    ext <;> simp [pureScalar]
  map_smul' c a := by
    ext <;> simp [pureScalar]

def strongBaseOperatorLinear
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    (Fin 3 → ℝ) →ₗ[ℝ]
      (TangentSpace 𝓘(ℝ,EModel q) (baseCoset n) →L[ℝ]
        TangentSpace 𝓘(ℝ,EModel q) (baseCoset n)) := by
  letI := a.quotientCharts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  let U := (euclideanModelEquiv q).toLinearEquiv
  exact (Module.End.toContinuousLinearMap (𝕜 := ℝ) (EModel q)).toLinearMap.comp
    ((U.conjAlgEquiv ℝ).toLinearMap.comp
      ((baseQuaternionAction hDesc hImm n d e q g a hq).toLinearMap.comp
        pureScalarLinear))

theorem strongBaseOperatorLinear_apply
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn z.1 =
      strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn z := rfl

theorem continuous_strongBaseUnitOperator
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    Continuous (strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  have h : Continuous (fun z : coefficientSphere =>
      strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn z.1) :=
    (strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn).continuous_of_finiteDimensional.comp
      continuous_subtype_val
  exact h.congr (fun z => strongBaseOperatorLinear_apply hLee hDesc hImm n d e q g a hq hn z)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseOperatorContinuous
