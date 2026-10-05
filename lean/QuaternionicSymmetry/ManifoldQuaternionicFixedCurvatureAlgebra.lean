import QuaternionicSymmetry.ManifoldQuaternionicKSWEinsteinAdapted
import QuaternionicSymmetry.ManifoldQuaternionicRiemannSymmetry
import QuaternionicSymmetry.ManifoldQuaternionicSymplecticCurvature
import QuaternionicSymmetry.QuaternionicManifoldModelProjection

/-! The actual tangent curvature, transported into the fixed quaternionic
model, satisfies the hypotheses of the algebraic curvature decomposition. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedCurvatureAlgebra
open ManifoldQuaternionicConnection ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWEinstein
open ManifoldQuaternionicKSWEinsteinAdapted ManifoldQuaternionicRiemannSymmetry
open ManifoldQuaternionicCurvatureProjection ManifoldQuaternionicSymplecticCurvature
open QuaternionicManifoldFixedNormalizer QuaternionicManifoldProjectiveStandardConnection
open QuaternionicManifoldModelProjection QuaternionicLieAlgebraProjection
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

def curvatureBilinear (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  let e := (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)
    (fixedTangentConjugation S Q p)).comp
      (((ContinuousLinearMap.compL ℝ E E (E →L[ℝ] E)).flip e).comp
        ((D.curvature Q p y).comp e))

theorem curvatureBilinear_apply (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E) :
    curvatureBilinear S Q D p y hy u v = fixedCurvature S Q D p y hy u v := rfl

theorem tensor_eq (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w z : E) :
    inner ℝ (curvatureBilinear S Q D p y hy u v w) z =
      riemann Q D p y hy
        (modelGauge S (Q.reduction.Q (achart E p)) u)
        (modelGauge S (Q.reduction.Q (achart E p)) v)
        (modelGauge S (Q.reduction.Q (achart E p)) w)
        (modelGauge S (Q.reduction.Q (achart E p)) z) := by
  rw [curvatureBilinear_apply, fixedCurvature_apply_adapted]
  let g := modelGauge S (Q.reduction.Q (achart E p))
  have he := g.symm.inner_map_map
    (adaptedCurvature Q D p y hy (g u) (g v) (g w)) (g z)
  simpa only [g.symm_apply_apply, riemann, g] using he

theorem skew_first (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E) :
    curvatureBilinear S Q D p y hy u v = -curvatureBilinear S Q D p y hy v u := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_right ℝ
  intro z
  simp only [ContinuousLinearMap.neg_apply, inner_neg_left, tensor_eq]
  exact riemann_skew_first Q D p y hy _ _ _ _

theorem skew_last (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w z : E) :
    inner ℝ (curvatureBilinear S Q D p y hy u v w) z =
      -inner ℝ (curvatureBilinear S Q D p y hy u v z) w := by
  simp only [tensor_eq]
  exact riemann_skew_last Q D p y hy _ _ _ _

theorem first_bianchi (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w : E) :
    curvatureBilinear S Q D p y hy u v w + curvatureBilinear S Q D p y hy v w u +
      curvatureBilinear S Q D p y hy w u v = 0 := by
  apply ext_inner_right ℝ
  intro z
  simp only [inner_add_left, inner_zero_left, tensor_eq]
  exact riemann_first_bianchi Q D p y hy _ _ _ _

theorem symplectic_commutes (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E) (a : Fin 3 → ℝ) :
    symplecticProjection S (curvatureBilinear S Q D p y hy u v) * synth S a =
      synth S a * symplecticProjection S (curvatureBilinear S Q D p y hy u v) := by
  let T := Q.reduction.Q (achart E p)
  let e := fixedSolderEquiv S Q p y hy
  let A := D.curvature Q p y (e.symm u) (e.symm v)
  have hA (b : Fin 3 → ℝ) : symplecticProjection T A * synth T b =
      synth T b * symplecticProjection T A := by
    dsimp only [A, T]
    rw [← symplecticCurvature_eq_projection Q D p y (e.symm u) (e.symm v) hy]
    exact symplecticCurvature_commutes Q D p y _ _ hy b
  change symplecticProjection S
      (QuaternionicIsometryNormalizer.conjugation (modelGauge S T).symm A) * synth S a =
    synth S a * symplecticProjection S
      (QuaternionicIsometryNormalizer.conjugation (modelGauge S T).symm A)
  rw [symplecticProjection_modelGauge S T A hA]
  exact modelGauge_symm_conjugation_commutes S T _ hA a

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedCurvatureAlgebra
