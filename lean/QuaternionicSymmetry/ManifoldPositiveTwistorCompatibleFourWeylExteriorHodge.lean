import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicHalf
import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylHodge

/-! The corrected four-dimensional Weyl endomorphism gives a genuine
exterior two-covector in the negative Hodge half of each Q-oriented frame. -/
namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylExteriorHodge

open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveTwistorCompatibleFourWeylOperator
open ManifoldPositiveTwistorCompatibleFourWeylHodge
open FourDimensionalExteriorHodge FourDimensionalQuaternionicHodgeFrame
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem correctedWeyl_negative_exteriorHodge
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v z : E) (hz : ‖z‖ = 1) :
    let b := frameBasis (P.tangent.reduction.Q (achart E p)) P.realDimension z hz
    frameStar b
      (HyperholomorphicExterior.form b.toBasis
        (correctedWeylOperator P p y hy u v).toLinearMap) =
    -HyperholomorphicExterior.form b.toBasis
      (correctedWeylOperator P p y hy u v).toLinearMap := by
  let b := frameBasis (P.tangent.reduction.Q (achart E p)) P.realDimension z hz
  let A := (correctedWeylOperator P p y hy u v).toLinearMap
  apply (coordinateEquiv b.toBasis).injective
  change coordinates b.toBasis
      (frameStar b (HyperholomorphicExterior.form b.toBasis A)) =
    coordinates b.toBasis (-HyperholomorphicExterior.form b.toBasis A)
  rw [coordinates_frameStar, map_neg,
    coordinates_operatorForm b A (correctedWeylOperator_skew P p y hy u v)]
  exact correctedWeyl_negative_coordinateHodge P p y hy u v z hz

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylExteriorHodge
