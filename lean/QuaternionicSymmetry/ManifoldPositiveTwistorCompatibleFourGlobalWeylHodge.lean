import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourCanonicalHodge
import QuaternionicSymmetry.ManifoldQuaternionicFourGlobalHodge
import QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeFiber

/-! Transport the corrected Weyl-output two-form from an adapted chart to
the genuine tangent fiber. This records the actual global Hodge sign, but
does not yet assert the vanishing of the opposite Weyl *input block*. -/

namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourGlobalWeylHodge

open FourDimensionalExteriorHodge
open FourDimensionalExteriorCanonicalHodge
open ManifoldQuaternionicFourGlobalHodge
open ManifoldQuaternionicFourHodgeOverlapExterior
open ManifoldQuaternionicFourTangentOrientation
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveTwistorCompatibleFourWeylOperator
open ManifoldPositiveTwistorCompatibleFourCanonicalHodge
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 600000

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The corrected Weyl skew form, now on the actual tangent fiber at the
point with local coordinate `y`. -/
def tangentCorrectedWeylForm
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hi : (extChartAt 𝓘(ℝ,E) p).symm y ∈
      P.tangent.frames.adaptedCore.baseSet (achart E p))
    (u v : E) :
    TwoForm (TangentSpace 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm y)) := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  let i := achart E p
  let b := (FourDimensionalQuaternionicHodgeFrame.frameBasis
    (P.tangent.reduction.Q i) P.realDimension unit unit_norm).toBasis
  let C := localToTangentEquiv P.tangent i x hi
  change TwoForm E
  exact pullbackTwoForm b C.symm.toLinearMap
    (HyperholomorphicExterior.form b
      (correctedWeylOperator P p y hy u v).toLinearMap)

/-- The output form of the corrected Weyl curvature belongs to the
negative half of the actual tangent-fiber Hodge star. -/
theorem tangentCorrectedWeylForm_negative
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hi : (extChartAt 𝓘(ℝ,E) p).symm y ∈
      P.tangent.frames.adaptedCore.baseSet (achart E p))
    (u v : E) :
    tangentHodgeStar P.tangent P.realDimension
      ((extChartAt 𝓘(ℝ,E) p).symm y)
      (tangentCorrectedWeylForm P p y hy hi u v) =
      -tangentCorrectedWeylForm P p y hy hi u v := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  let i := achart E p
  let b := (FourDimensionalQuaternionicHodgeFrame.frameBasis
    (P.tangent.reduction.Q i) P.realDimension unit unit_norm).toBasis
  let C := localToTangentEquiv P.tangent i x hi
  let β := HyperholomorphicExterior.form b
    (correctedWeylOperator P p y hy u v).toLinearMap
  have hβ : canonicalStar (P.tangent.reduction.Q i) P.realDimension β = -β := by
    dsimp only [β, b, i]
    exact correctedWeyl_canonicalStar_negative P p y hy u v
      (unit : E) (unit_norm (E := E))
  have hp : pullbackTwoForm b C.toLinearMap
      (tangentCorrectedWeylForm P p y hy hi u v) = β := by
    apply ExteriorDuality.twoform_ext b
    intro a c
    rw [evaluate_pullbackTwoForm]
    dsimp only [tangentCorrectedWeylForm, id_eq]
    rw [evaluate_pullbackTwoForm]
    change BilinearExterior.evaluate (C.symm (C a)) (C.symm (C c)) β =
      BilinearExterior.evaluate a c β
    rw [C.symm_apply_apply, C.symm_apply_apply]
  have h := tangentHodgeStar_local P.tangent P.realDimension i x hi b
    (tangentCorrectedWeylForm P p y hy hi u v)
  rw [hp, hβ] at h
  apply ExteriorDuality.twoform_ext b
  intro a c
  have he := congrArg (fun θ : TwoForm E =>
    BilinearExterior.evaluate (C.symm a) (C.symm c) θ) h
  change BilinearExterior.evaluate (C.symm a) (C.symm c)
      (pullbackTwoForm b C.toLinearMap
        (tangentHodgeStar P.tangent P.realDimension x
          (tangentCorrectedWeylForm P p y hy hi u v))) =
    BilinearExterior.evaluate (C.symm a) (C.symm c) (-β) at he
  rw [evaluate_pullbackTwoForm] at he
  have hp' := congrArg (fun θ : TwoForm E =>
    BilinearExterior.evaluate (C.symm a) (C.symm c) θ) hp
  change BilinearExterior.evaluate (C.symm a) (C.symm c)
      (pullbackTwoForm b C.toLinearMap
        (tangentCorrectedWeylForm P p y hy hi u v)) =
    BilinearExterior.evaluate (C.symm a) (C.symm c) β at hp'
  rw [evaluate_pullbackTwoForm] at hp'
  simp only [map_neg] at he
  have hfinal := he.trans (congrArg Neg.neg hp').symm
  change BilinearExterior.evaluate (C (C.symm a)) (C (C.symm c))
      (tangentHodgeStar P.tangent P.realDimension x
        (tangentCorrectedWeylForm P p y hy hi u v)) =
    -BilinearExterior.evaluate (C (C.symm a)) (C (C.symm c))
      (tangentCorrectedWeylForm P p y hy hi u v) at hfinal
  rw [C.apply_symm_apply, C.apply_symm_apply] at hfinal
  simpa only [map_neg] using hfinal

/-- Reversing the global quaternionic orientation makes the actual Weyl
output self-dual, the sign convention in Derdzinski 33.4(a). The local
orientation reversal is certified by `frameStar_swap01`. -/
theorem tangentCorrectedWeylForm_opposite_positive
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hi : (extChartAt 𝓘(ℝ,E) p).symm y ∈
      P.tangent.frames.adaptedCore.baseSet (achart E p))
    (u v : E) :
    -(tangentHodgeStar P.tangent P.realDimension
      ((extChartAt 𝓘(ℝ,E) p).symm y)
      (tangentCorrectedWeylForm P p y hy hi u v)) =
      tangentCorrectedWeylForm P p y hy hi u v := by
  rw [tangentCorrectedWeylForm_negative P p y hy hi u v]
  exact neg_neg _

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourGlobalWeylHodge
