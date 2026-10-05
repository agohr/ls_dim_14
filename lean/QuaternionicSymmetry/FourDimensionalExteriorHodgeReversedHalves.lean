import QuaternionicSymmetry.FourDimensionalExteriorHodgeOrientationFlip
import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicHalf
import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylExteriorHodge

/-! Actual exterior-form eigenspace signs under an explicitly verified
orientation reversal. Which orientation LeBrun calls the negative-spinor
orientation remains a separate source comparison. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorHodgeReversedHalves

open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorHodgeOrientationFlip
open FourDimensionalQuaternionicHodgeFrame
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveTwistorCompatibleFourWeylOperator
open ManifoldPositiveTwistorCompatibleFourWeylExteriorHodge
open scoped Manifold ContDiff
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

theorem quaternionicForms_negative_after_orientationFlip
    (Q : QuaternionicStructure V) (hdim : Module.finrank ℝ V = 4)
    (v : V) (hv : ‖v‖ = 1) (α : TwoForm V)
    (hα : α ∈ (quaternionicSpan Q).map
      (operatorForm (frameBasis Q hdim v hv).toBasis)) :
    frameStar (swap01 (frameBasis Q hdim v hv)) α = -α := by
  let b := frameBasis Q hdim v hv
  have hp : α ∈ positiveExteriorHalf b := by
    rw [positiveExteriorHalf_eq_quaternionicFormImage Q hdim v hv]
    exact hα
  rw [frameStar_swap01, (mem_positiveExteriorHalf b α).mp hp]

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem correctedWeyl_positive_after_orientationFlip
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v z : E) (hz : ‖z‖ = 1) :
    let b := frameBasis (P.tangent.reduction.Q (achart E p)) P.realDimension z hz
    frameStar (swap01 b)
      (HyperholomorphicExterior.form b.toBasis
        (correctedWeylOperator P p y hy u v).toLinearMap) =
    HyperholomorphicExterior.form b.toBasis
      (correctedWeylOperator P p y hy u v).toLinearMap := by
  let b := frameBasis (P.tangent.reduction.Q (achart E p)) P.realDimension z hz
  change frameStar (swap01 b)
    (HyperholomorphicExterior.form b.toBasis
      (correctedWeylOperator P p y hy u v).toLinearMap) =
    HyperholomorphicExterior.form b.toBasis
      (correctedWeylOperator P p y hy u v).toLinearMap
  rw [frameStar_swap01,
    correctedWeyl_negative_exteriorHodge P p y hy u v z hz]
  simp [b]

end
end QuaternionicSymmetry.FourDimensionalExteriorHodgeReversedHalves
