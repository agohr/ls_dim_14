import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourGeometry
import QuaternionicSymmetry.ManifoldQuaternionicMetricCurvature
import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionLaws
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal

/-! The corrected four-dimensional Weyl vector as an actual bounded skew
endomorphism in the quaternionic centralizer. -/
namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylOperator

open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicMetricCurvature
open QuaternionicLieAlgebraProjection
open ManifoldQuaternionicRankThreeOrthogonal
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open VectorBundleFrameTransitions
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def wedgeLinear (u v : E) : E →ₗ[ℝ] E where
  toFun w := (inner ℝ v w) • u - (inner ℝ u w) • v
  map_add' w z := by simp [inner_add_right, add_smul]; abel
  map_smul' t w := by simp [real_inner_smul_right]; module

def correctedWeylOperator
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v : E) : E →L[ℝ] E :=
  P.connection.curvature P.tangent p y
      ((solderEquiv P.tangent p y hy).symm u)
      ((solderEquiv P.tangent p y hy).symm v) -
    (localScalarCurvature P.tangent P.connection p y hy / 12) •
      (wedgeLinear u v).toContinuousLinearMap

theorem correctedWeylOperator_apply
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v w : E) :
    correctedWeylOperator P p y hy u v w =
      correctedWeylVector P.toPositiveQuaternionicKahlerGeometry
        p y hy u v w := by
  rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem wedgeLinear_skew (u v w z : E) :
    inner ℝ (wedgeLinear u v w) z = -inner ℝ w (wedgeLinear u v z) := by
  simp only [wedgeLinear, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm w u, real_inner_comm w v]
  ring

theorem correctedWeylOperator_skew
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v w z : E) :
    inner ℝ (correctedWeylOperator P p y hy u v w) z =
      -inner ℝ w (correctedWeylOperator P p y hy u v z) := by
  have hc := tangentCurvature_skew P.tangent P.connection p y
    ((solderEquiv P.tangent p y hy).symm u)
    ((solderEquiv P.tangent p y hy).symm v) w z hy
  have hw := wedgeLinear_skew u v w z
  simp only [correctedWeylOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,
    inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right] at *
  change inner ℝ
      (P.connection.curvature P.tangent p y
        ((solderEquiv P.tangent p y hy).symm u)
        ((solderEquiv P.tangent p y hy).symm v) w) z -
      (localScalarCurvature P.tangent P.connection p y hy / 12) *
        inner ℝ (wedgeLinear u v w) z =
      -(inner ℝ w
        (P.connection.curvature P.tangent p y
          ((solderEquiv P.tangent p y hy).symm u)
          ((solderEquiv P.tangent p y hy).symm v) z) -
        (localScalarCurvature P.tangent P.connection p y hy / 12) *
          inner ℝ w (wedgeLinear u v z))
  rw [hw]
  linear_combination hc

theorem correctedWeylOperator_commutes_synth
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v : E) (a : Fin 3 → ℝ) :
    correctedWeylOperator P p y hy u v *
      synth (P.tangent.reduction.Q (achart E p)) a =
    synth (P.tangent.reduction.Q (achart E p)) a *
      correctedWeylOperator P p y hy u v := by
  ext w
  change correctedWeylOperator P p y hy u v
      (synth (P.tangent.reduction.Q (achart E p)) a w) =
    synth (P.tangent.reduction.Q (achart E p)) a
      (correctedWeylOperator P p y hy u v w)
  rw [correctedWeylOperator_apply,
    correctedWeylOperator_apply]
  exact P.oppositeWeyl p y hy u v a w

theorem correctedWeylOperator_mem_skewCentralizer
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v : E) :
    (correctedWeylOperator P p y hy u v).toLinearMap ∈
      (P.tangent.reduction.Q (achart E p)).skewCentralizer := by
  let S := P.tangent.reduction.Q (achart E p)
  apply (S.mem_skewCentralizer_iff _).mpr
  refine ⟨correctedWeylOperator_skew P p y hy u v, ?_, ?_⟩
  · intro w
    have h := congrArg (fun A : E →L[ℝ] E => A w)
      (correctedWeylOperator_commutes_synth P p y hy u v
        (Pi.basisFun ℝ (Fin 3) 0))
    simpa only [synth_basis, quaternionicGenerator, Matrix.cons_val_zero,
      ContinuousLinearMap.mul_apply, S] using h
  · intro w
    have h := congrArg (fun A : E →L[ℝ] E => A w)
      (correctedWeylOperator_commutes_synth P p y hy u v
        (Pi.basisFun ℝ (Fin 3) 1))
    simpa only [synth_basis, quaternionicGenerator,
      ContinuousLinearMap.mul_apply, S] using h

theorem correctedWeylOperator_scalarProjection_zero
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v : E) :
    scalarProjection (P.tangent.reduction.Q (achart E p))
      (correctedWeylOperator P p y hy u v) = 0 := by
  exact scalarProjection_eq_zero_of_commutes
    (P.tangent.reduction.Q (achart E p)) _
    (correctedWeylOperator_commutes_synth P p y hy u v)

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylOperator
