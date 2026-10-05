import QuaternionicSymmetry.AlgebraicRiemannPairSymmetry
import QuaternionicSymmetry.ManifoldQuaternionicFirstBianchi
import QuaternionicSymmetry.ManifoldQuaternionicMetricCurvature
import QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature

/-! The actual metric and torsion-free tangent connection has all algebraic
Riemann tensor symmetries in an adapted orthonormal frame. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicRiemannSymmetry
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicFirstBianchi
open ManifoldQuaternionicMetricCurvature
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

def riemann (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v w z : E) : ℝ :=
  inner ℝ (adaptedCurvature Q D p y hy u v w) z

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem riemann_first_bianchi (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w z : E) :
    riemann Q D p y hy u v w z + riemann Q D p y hy v w u z +
      riemann Q D p y hy w u v z = 0 := by
  let e := solderEquiv Q p y hy
  have h := tangentCurvature_first_bianchi Q D p y
    (e.symm u) (e.symm v) (e.symm w) hy
  have h' := congrArg (fun t : E => inner ℝ t z) h
  have he (a : E) : solder Q p y (e.symm a) = a := e.apply_symm_apply a
  rw [he w, he u, he v] at h'
  simpa [riemann, adaptedCurvature, e, inner_add_left] using h'

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem riemann_skew_first (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w z : E) :
    riemann Q D p y hy u v w z = -riemann Q D p y hy v u w z := by
  have h := LocalConnection.curvature_antisymm (D.form p) y
    ((solderEquiv Q p y hy).symm u) ((solderEquiv Q p y hy).symm v)
  simp only [riemann, adaptedCurvature, CompatibleTangentConnection.curvature,
    h, ContinuousLinearMap.neg_apply, inner_neg_left]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem riemann_skew_last (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w z : E) :
    riemann Q D p y hy u v w z = -riemann Q D p y hy u v z w := by
  have h := tangentCurvature_skew Q D p y
    ((solderEquiv Q p y hy).symm u) ((solderEquiv Q p y hy).symm v)
    w z hy
  have hcomm := real_inner_comm w
    (D.curvature Q p y ((solderEquiv Q p y hy).symm u)
      ((solderEquiv Q p y hy).symm v) z)
  change riemann Q D p y hy u v w z +
    inner ℝ w (D.curvature Q p y ((solderEquiv Q p y hy).symm u)
      ((solderEquiv Q p y hy).symm v) z) = 0 at h
  have hcomm' : inner ℝ w (D.curvature Q p y ((solderEquiv Q p y hy).symm u)
      ((solderEquiv Q p y hy).symm v) z) = riemann Q D p y hy u v z w := hcomm.symm
  rw [hcomm'] at h
  exact eq_neg_of_add_eq_zero_left h

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem riemann_pair_symmetry (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w z : E) :
    riemann Q D p y hy u v w z = riemann Q D p y hy w z u v :=
  AlgebraicRiemannPairSymmetry.pair_symmetry (riemann Q D p y hy)
    (riemann_skew_first Q D p y hy) (riemann_skew_last Q D p y hy)
    (riemann_first_bianchi Q D p y hy) u v w z

omit [Nontrivial E] in
theorem localRicci_symmetric (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    localRicci Q D p y hy v w = localRicci Q D p y hy w v := by
  unfold localRicci
  apply Finset.sum_congr rfl
  intro a _
  let e := stdOrthonormalBasis ℝ E a
  change riemann Q D p y hy e v w e = riemann Q D p y hy e w v e
  calc
    riemann Q D p y hy e v w e = riemann Q D p y hy w e e v :=
      riemann_pair_symmetry Q D p y hy e v w e
    _ = -riemann Q D p y hy e w e v := riemann_skew_first Q D p y hy w e e v
    _ = riemann Q D p y hy e w v e := by
      rw [riemann_skew_last Q D p y hy e w e v]
      ring

omit [Nontrivial E] in
theorem ricciOperator_selfAdjoint (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    inner ℝ (ricciOperator Q D p y hy v) w =
      inner ℝ v (ricciOperator Q D p y hy w) := by
  rw [ricciOperator_inner, real_inner_comm,
    ricciOperator_inner]
  exact localRicci_symmetric Q D p y hy v w

omit [Nontrivial E] in
theorem ricciBilinear_symmetric (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    ricciBilinear Q D p y hy v w = ricciBilinear Q D p y hy w v :=
  localRicci_symmetric Q D p y hy v w

omit [Nontrivial E] in
theorem scalarCurvature_eq_ricci_trace (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    localScalarCurvature Q D p y hy =
      LinearMap.trace ℝ E (ricciOperator Q D p y hy) := by
  exact (ricciOperator_trace_eq_diagonal Q D p y hy
    (stdOrthonormalBasis ℝ E)).symm

omit [Nontrivial E] in
theorem scalarCurvature_eq_riemann_double_sum (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    localScalarCurvature Q D p y hy =
      ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          riemann Q D p y hy (stdOrthonormalBasis ℝ E b)
            (stdOrthonormalBasis ℝ E a) (stdOrthonormalBasis ℝ E a)
            (stdOrthonormalBasis ℝ E b) := rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicRiemannSymmetry
