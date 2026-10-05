import QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryDerivativeSquare
import QuaternionicSymmetry.CompactSymplecticProjectorPointSymmetryQuaternionicPlane
import QuaternionicSymmetry.CompactSymplecticProjectorPreferredContinuousPlane
import QuaternionicSymmetry.LinearConjugationSubmoduleNaturality
import QuaternionicSymmetry.LinearContinuousConjugationSubmoduleNaturality

/-! The actual point reflection transports the preferred strong-coordinate
projector Q-plane by the conjugation of its genuine strong differential. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryPreferredPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongPointSymmetry
open CompactSymplecticProjectorStrongPointSymmetryDerivativeSquare
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticProjectorPointSymmetryQuaternionicPlane
open CompactSymplecticProjectorReflection
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorPreferredContinuousPlane
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open LinearConjugationSubmoduleNaturality
open LinearContinuousConjugationSubmoduleNaturality
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem pointSymmetry_preferredPlane_invariant
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    let T := strongPointSymmetryDiffeomorph hLee hDesc hImm n d e q g a hq hn x
    preferredContinuousImaginaryPlane hDesc hImm n d e q g a hq hn
      (pointSymmetry n x y) =
    Submodule.map
      ((T.mfderivToContinuousLinearEquiv (by simp) y).conjContinuousAlgEquiv.toLinearMap)
      (preferredContinuousImaginaryPlane hDesc hImm n d e q g a hq hn y) := by
  letI := a.quotientCharts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  let T := strongPointSymmetryDiffeomorph hLee hDesc hImm n d e q g a hq hn x
  let U := euclideanModelEquiv q
  let C := translationTangentEquiv n d e q g a (reflectionElement n x) y
  let D := T.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0) y
  let P := quotientImaginaryPlane hDesc hImm n d e q g a hq hn y
  have hcomm : C.trans U = U.trans D := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact pointSymmetry_derivative_coordinate_square
      hLee hDesc hImm n d e q g a hq hn x y v
  have hcommL : C.toLinearEquiv.trans U.toLinearEquiv =
      U.toLinearEquiv.trans D.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L : RModel q ≃L[ℝ] EModel q => L v) hcomm
  have hOld := pointSymmetry_preserves_quotientImaginaryPlane
    hDesc hImm n d e q g a hq hn x y
  change ((quotientImaginaryPlane hDesc hImm n d e q g a hq hn
      (pointSymmetry n x y)).map
        (U.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap).map
      (Module.End.toContinuousLinearMap (𝕜 := ℝ) (EModel q)).toLinearMap = _
  rw [hOld]
  change ((P.map (C.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap).map
      (U.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap |>.map
      (Module.End.toContinuousLinearMap (𝕜 := ℝ) (EModel q)).toLinearMap) =
    ((P.map (U.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap |>.map
      (Module.End.toContinuousLinearMap (𝕜 := ℝ) (EModel q)).toLinearMap).map
        D.conjContinuousAlgEquiv.toLinearMap)
  rw [submodule_map_conj_commutes U.toLinearEquiv C.toLinearEquiv D.toLinearEquiv
    hcommL]
  exact map_toContinuous_conj (V := EModel q) D
    (P.map (U.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryPreferredPlane
