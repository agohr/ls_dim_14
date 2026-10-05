import QuaternionicSymmetry.FourDimensionalHodgeOrthogonalSum
import QuaternionicSymmetry.ManifoldQuaternionicFourFormTransitions

/-! The actual adapted SO(3) overlap preserves the quaternionic averaging
formula on bilinear two-forms. This is the algebraic naturality needed to glue
the pointwise exterior Hodge operators. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourHodgeOverlapBilinear

open FourDimensionalExteriorCanonicalHodge
open FourDimensionalHodgeOrthogonalSum
open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourFormTransitions
open VectorBundleFrameTransitions
open scoped Manifold ContDiff BigOperators
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def generatorBilinearSum (S : QuaternionicStructure E)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (v w : E) : ℝ :=
  ∑ t : Fin 3, B (quaternionicGenerator S t v)
    (quaternionicGenerator S t w)

theorem generatorBilinearSum_eq (S : QuaternionicStructure E)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (v w : E) :
    generatorBilinearSum S B v w =
      B (S.I v) (S.I w) + B (S.J v) (S.J w) +
        B (S.K v) (S.K w) := by
  simp [generatorBilinearSum, Fin.sum_univ_succ,
    quaternionicGenerator]
  abel

def quaternionicAverage (S : QuaternionicStructure E)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • (B -
    bilinearPullback S.I.toLinearEquiv.toLinearMap B -
    bilinearPullback S.J.toLinearEquiv.toLinearMap B -
    bilinearPullback S.K.toLinearEquiv.toLinearMap B)

theorem quaternionicAverage_apply (S : QuaternionicStructure E)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (v w : E) :
    quaternionicAverage S B v w =
      (B v w - generatorBilinearSum S B v w) / 2 := by
  simp [quaternionicAverage, generatorBilinearSum_eq,
    bilinearPullback_apply, smul_eq_mul]
  ring

theorem generatorBilinearSum_transition
    (Q : SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (v w : E) :
    generatorBilinearSum (Q.reduction.Q i)
      (bilinearPullback (Q.frames.coordChange i j x).toLinearMap B) v w =
    generatorBilinearSum (Q.reduction.Q j) B
      (Q.frames.coordChange i j x v) (Q.frames.coordChange i j x w) := by
  let R := rotationMatrix Q i j x
  let T := Q.frames.coordChange i j x
  let a : Fin 3 → E := fun t => quaternionicGenerator (Q.reduction.Q j) t (T v)
  let b : Fin 3 → E := fun t => quaternionicGenerator (Q.reduction.Q j) t (T w)
  change (∑ s : Fin 3,
    B (T (quaternionicGenerator (Q.reduction.Q i) s v))
      (T (quaternionicGenerator (Q.reduction.Q i) s w))) =
    ∑ t : Fin 3, B (a t) (b t)
  dsimp only [T]
  simp_rw [generator_transition Q i j x hi hj]
  exact bilinear_sum_orthogonal R
    (rotationMatrix_rows_orthogonal Q i j x hi hj) B a b

theorem quaternionicAverage_transition
    (Q : SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (v w : E) :
    quaternionicAverage (Q.reduction.Q i)
      (bilinearPullback (Q.frames.coordChange i j x).toLinearMap B) v w =
    quaternionicAverage (Q.reduction.Q j) B
      (Q.frames.coordChange i j x v) (Q.frames.coordChange i j x w) := by
  rw [quaternionicAverage_apply, quaternionicAverage_apply]
  rw [generatorBilinearSum_transition Q i j x hi hj B v w]
  rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicFourHodgeOverlapBilinear
