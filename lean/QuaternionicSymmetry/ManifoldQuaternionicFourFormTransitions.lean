import QuaternionicSymmetry.ManifoldQuaternionicFourForm
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal

/-! The actual rank-three transition written as an orthogonal matrix. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourFormTransitions

open Matrix QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open VectorBundleFrameTransitions
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

def rotationMatrix (i j : atlas E M) (x : M) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun t s => Q.reduction.rankThreeCoordChange i j x (Pi.basisFun ℝ (Fin 3) s) t

theorem rotationMatrix_mulVec (i j : atlas E M) (x : M) (a : Fin 3 → ℝ) :
    rotationMatrix Q i j x *ᵥ a = Q.reduction.rankThreeCoordChange i j x a := by
  funext t
  have hrepr : a = ∑ s : Fin 3, a s • Pi.basisFun ℝ (Fin 3) s := by
    simpa [Pi.basisFun_repr] using ((Pi.basisFun ℝ (Fin 3)).sum_repr a).symm
  conv_rhs => rw [hrepr]
  simp [rotationMatrix, Matrix.mulVec, dotProduct, map_sum, map_smul,
    Finset.sum_apply, mul_comm]

theorem rotationMatrix_orthogonal (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    (rotationMatrix Q i j x)ᵀ * rotationMatrix Q i j x = 1 := by
  ext s t
  have h := rankThreeCoordChange_dot Q i j x hi hj
    (Pi.basisFun ℝ (Fin 3) s) (Pi.basisFun ℝ (Fin 3) t)
  simpa [rotationMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Pi.basisFun_apply, Pi.single_apply, Finset.sum_ite_eq',
    Matrix.one_apply, eq_comm] using h

theorem rotationMatrix_rows_orthogonal (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    rotationMatrix Q i j x * (rotationMatrix Q i j x)ᵀ = 1 := by
  exact mul_eq_one_comm.mp (rotationMatrix_orthogonal Q i j x hi hj)

theorem generator_transition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (s : Fin 3) (v : E) :
    Q.frames.coordChange i j x (quaternionicGenerator (Q.reduction.Q i) s v) =
      ∑ t : Fin 3, (rotationMatrix Q i j x) t s •
        quaternionicGenerator (Q.reduction.Q j) t
          (Q.frames.coordChange i j x v) := by
  have h := synth_rankThreeCoordChange_eval Q i j x hi hj
    (Pi.basisFun ℝ (Fin 3) s) v
  rw [← rotationMatrix_mulVec] at h
  rw [synth_basis] at h
  have hcol : rotationMatrix Q i j x *ᵥ Pi.basisFun ℝ (Fin 3) s =
      fun t => rotationMatrix Q i j x t s := by
    funext t
    simp [Matrix.mulVec, dotProduct, Pi.basisFun_apply, Pi.single_apply]
  rw [hcol, synth_apply] at h
  simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply] using h.symm

def frameKahler (i : atlas E M) (t : Fin 3) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  (1 / 2 : ℝ) • LocalConnectionForms.alternatingPart
    ((innerSL ℝ).comp (quaternionicGenerator (Q.reduction.Q i) t))

theorem frameKahler_transition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) (s : Fin 3) :
    frameKahler Q i s =
      ∑ t : Fin 3, (rotationMatrix Q i j x) t s •
        (frameKahler Q j t).compContinuousLinearMap
          (Q.frames.coordChange i j x) := by
  ext v
  let L := Q.frames.coordChange i j x
  have hleft := Q.transition_inner i j x hi hj
    (quaternionicGenerator (Q.reduction.Q i) s (v 0)) (v 1)
  have hright := Q.transition_inner i j x hi hj
    (quaternionicGenerator (Q.reduction.Q i) s (v 1)) (v 0)
  rw [generator_transition Q i j x hi hj s (v 0)] at hleft
  rw [generator_transition Q i j x hi hj s (v 1)] at hright
  rw [ContinuousAlternatingMap.sum_apply]
  simp only [frameKahler,
    ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    LocalConnectionForms.alternatingPart_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  change (1 / 2 : ℝ) *
      (inner ℝ (quaternionicGenerator (Q.reduction.Q i) s (v 0)) (v 1) -
        inner ℝ (quaternionicGenerator (Q.reduction.Q i) s (v 1)) (v 0)) =
    ∑ t : Fin 3, rotationMatrix Q i j x t s *
      ((1 / 2 : ℝ) *
        (inner ℝ (quaternionicGenerator (Q.reduction.Q j) t (L (v 0))) (L (v 1)) -
          inner ℝ (quaternionicGenerator (Q.reduction.Q j) t (L (v 1))) (L (v 0))))
  rw [← hleft, ← hright]
  simp only [sum_inner, real_inner_smul_left]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem chartKahler_eq_frameKahler (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (t : Fin 3) :
    ManifoldQuaternionicFourForm.chartKahler Q i x t =
      (frameKahler Q i t).compContinuousLinearMap (Q.frames.toFrame i x) := by
  ext v
  simp only [ManifoldQuaternionicFourForm.chartKahler, frameKahler,
    ContinuousAlternatingMap.smul_apply,
    LocalConnectionForms.alternatingPart_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply,
    ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent.chartMetricForm_apply,
    innerSL_apply_apply]
  change (1 / 2 : ℝ) *
      (inner ℝ (Q.frames.toFrame i x
        (Q.toSmoothAlmostQuaternionicTangent.chartGenerator i t x (v 0)))
        (Q.frames.toFrame i x (v 1)) -
      inner ℝ (Q.frames.toFrame i x
        (Q.toSmoothAlmostQuaternionicTangent.chartGenerator i t x (v 1)))
        (Q.frames.toFrame i x (v 0))) = _
  simp only [ManifoldQuaternionicReduction.SmoothAlmostQuaternionicTangent.chartGenerator,
    ContinuousLinearMap.comp_apply, Q.frames.to_from i x hi,
    Function.comp_apply, smul_eq_mul]

end
end QuaternionicSymmetry.ManifoldQuaternionicFourFormTransitions
