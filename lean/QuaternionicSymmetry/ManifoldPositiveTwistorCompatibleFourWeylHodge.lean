import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylOperator
import QuaternionicSymmetry.FourDimensionalQuaternionicHodgeFrame

/-! In every actual local quaternionic orthonormal four-frame, the corrected
Weyl endomorphism has negative coordinate Hodge star. This is an algebraic
statement about its skew two-form, not a twistor-integrability assertion. -/
namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylHodge

open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveTwistorCompatibleFourWeylOperator
open FourDimensionalQuaternionicHodgeFrame
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem correctedWeyl_negative_coordinateHodge
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v z : E) (hz : ‖z‖ = 1) :
    FourDimensionalCoordinateHodge.star
      (operatorTwoCoords
        (frameBasis (P.tangent.reduction.Q (achart E p)) P.realDimension z hz)
        (correctedWeylOperator P p y hy u v).toLinearMap) =
      -operatorTwoCoords
        (frameBasis (P.tangent.reduction.Q (achart E p)) P.realDimension z hz)
        (correctedWeylOperator P p y hy u v).toLinearMap := by
  exact centralizer_coordinates_negative
    (P.tangent.reduction.Q (achart E p)) P.realDimension z hz _
    (correctedWeylOperator_mem_skewCentralizer P p y hy u v)

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylHodge
