import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylOperator
import QuaternionicSymmetry.ManifoldQuaternionicRiemannSymmetry

/-! Pair symmetry for the actual scalar-corrected curvature. This is the
internal bridge needed to turn a Weyl output-half statement into an
input-block statement; no classification premise is used. -/

namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylPairSymmetry

open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveTwistorCompatibleFourWeylOperator
open ManifoldQuaternionicRiemannSymmetry
open ManifoldQuaternionicScalarCurvature
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem correctedWeylOperator_pair_symmetry
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v w z : E) :
    inner ℝ (correctedWeylOperator P p y hy u v w) z =
      inner ℝ (correctedWeylOperator P p y hy w z u) v := by
  have h := riemann_pair_symmetry P.tangent P.connection p y hy u v w z
  change inner ℝ (adaptedCurvature P.tangent P.connection p y hy u v w) z =
    inner ℝ (adaptedCurvature P.tangent P.connection p y hy w z u) v at h
  rw [correctedWeylOperator_apply, correctedWeylOperator_apply]
  simp only [correctedWeylVector, inner_sub_left, real_inner_smul_left]
  rw [h, real_inner_comm z u, real_inner_comm z v,
    real_inner_comm w u, real_inner_comm w v]
  ring

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylPairSymmetry
