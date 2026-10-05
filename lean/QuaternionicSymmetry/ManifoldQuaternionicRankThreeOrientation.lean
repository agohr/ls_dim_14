import QuaternionicSymmetry.ManifoldQuaternionicFourFormTransitions
import Mathlib.LinearAlgebra.CrossProduct

/-! Orientation of the quaternionic rank-three transition. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrientation

open Matrix VectorBundleFrameTransitions
  VectorBundleFrameTransitions.QuaternionicFrameReduction
  QuaternionicSymmetry.ManifoldQuaternionicFourFormTransitions
  QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
open scoped ContDiff Matrix Manifold

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem generator_commutator_basis (S : QuaternionicStructure E)
    (s t : Fin 3) :
    quaternionicGenerator S s * quaternionicGenerator S t -
      quaternionicGenerator S t * quaternionicGenerator S s =
      (2 : ℝ) • synth S
        (crossProduct (Pi.basisFun ℝ (Fin 3) s)
          (Pi.basisFun ℝ (Fin 3) t)) := by
  fin_cases s <;> fin_cases t <;>
    simp [crossProduct, Pi.basisFun_apply,
      quaternionicGenerator, synth_apply, Fin.sum_univ_succ]
  all_goals
    ext v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply]
    simp [S.K_apply, S.J_I_anti, S.I_sq, S.J_sq]
    module

omit [FiniteDimensional ℝ E] in
theorem synth_commutator_cross (S : QuaternionicStructure E)
    (a b : Fin 3 → ℝ) :
    synth S a * synth S b - synth S b * synth S a =
      (2 : ℝ) • synth S (crossProduct a b) := by
  let L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] (E →L[ℝ] E) :=
    LinearMap.mk₂ ℝ
      (fun x y => synth S x * synth S y - synth S y * synth S x)
      (by intros; simp [map_add, add_mul, mul_add]; abel)
      (by intros; simp [map_smul]; module)
      (by intros; simp [map_add, add_mul, mul_add]; abel)
      (by intros; simp [map_smul]; module)
  let R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] (E →L[ℝ] E) :=
    LinearMap.mk₂ ℝ
      (fun x y => (2 : ℝ) • synth S (crossProduct x y))
      (by intros; simp [map_add, smul_add])
      (by intros; simp [map_smul, smul_smul, mul_comm])
      (by intros; simp [map_add, smul_add])
      (by intros; simp [map_smul, smul_smul, mul_comm])
  have h : L = R := by
    apply (Pi.basisFun ℝ (Fin 3)).ext
    intro s
    apply (Pi.basisFun ℝ (Fin 3)).ext
    intro t
    change synth S ((Pi.basisFun ℝ (Fin 3)) s) *
        synth S ((Pi.basisFun ℝ (Fin 3)) t) -
      synth S ((Pi.basisFun ℝ (Fin 3)) t) *
        synth S ((Pi.basisFun ℝ (Fin 3)) s) =
      (2 : ℝ) • synth S
        (crossProduct ((Pi.basisFun ℝ (Fin 3)) s)
          ((Pi.basisFun ℝ (Fin 3)) t))
    rw [synth_basis, synth_basis]
    exact generator_commutator_basis S s t
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem rankThreeCoordChange_cross (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (a b : Fin 3 → ℝ) :
    Q.reduction.rankThreeCoordChange i j x (crossProduct a b) =
      crossProduct (Q.reduction.rankThreeCoordChange i j x a)
        (Q.reduction.rankThreeCoordChange i j x b) := by
  let A := (transitionAtlas Q.frames.adaptedCore).adjointCoordChange i j x
  let Ri := Q.reduction.rankThreeCoordChange i j x
  have h₁ := synth_rankThreeCoordChange Q i j x hi hj a
  have h₂ := synth_rankThreeCoordChange Q i j x hi hj b
  have h₃ := synth_rankThreeCoordChange Q i j x hi hj (crossProduct a b)
  have heq : (2 : ℝ) • synth (Q.reduction.Q j) (Ri (crossProduct a b)) =
      (2 : ℝ) • synth (Q.reduction.Q j) (crossProduct (Ri a) (Ri b)) := by
    calc
      _ = A ((2 : ℝ) • synth (Q.reduction.Q i) (crossProduct a b)) := by
        rw [map_smul, h₃]
      _ = A (synth (Q.reduction.Q i) a * synth (Q.reduction.Q i) b -
          synth (Q.reduction.Q i) b * synth (Q.reduction.Q i) a) := by
        rw [synth_commutator_cross]
      _ = A (synth (Q.reduction.Q i) a) * A (synth (Q.reduction.Q i) b) -
          A (synth (Q.reduction.Q i) b) * A (synth (Q.reduction.Q i) a) := by
        rw [map_sub, adjointCoordChange_mul Q.frames.adaptedCore i j x hi hj,
          adjointCoordChange_mul Q.frames.adaptedCore i j x hi hj]
      _ = synth (Q.reduction.Q j) (Ri a) * synth (Q.reduction.Q j) (Ri b) -
          synth (Q.reduction.Q j) (Ri b) * synth (Q.reduction.Q j) (Ri a) := by
        rw [h₁, h₂]
      _ = _ := synth_commutator_cross _ (Ri a) (Ri b)
  have heq' := (smul_right_injective (E →L[ℝ] E)
    (by norm_num : (2 : ℝ) ≠ 0)) heq
  have h := congrArg (coeff (Q.reduction.Q j)) heq'
  simpa only [coeff_synth] using h

private theorem basis_cross_zero_one :
    crossProduct (Pi.basisFun ℝ (Fin 3) 0)
      (Pi.basisFun ℝ (Fin 3) 1) = Pi.basisFun ℝ (Fin 3) 2 := by
  funext t
  fin_cases t <;> simp [crossProduct, Pi.basisFun_apply]

theorem rotationMatrix_det_one (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    (rotationMatrix Q i j x).det = 1 := by
  let R := rotationMatrix Q i j x
  let c (t : Fin 3) : Fin 3 → ℝ := R *ᵥ Pi.basisFun ℝ (Fin 3) t
  have hcols : Rᵀ = ![c 0, c 1, c 2] := by
    ext s t
    fin_cases s <;>
      simp [c, Pi.basisFun_apply,
        Matrix.transpose_apply]
  have hcross : crossProduct (c 0) (c 1) = c 2 := by
    change crossProduct (rotationMatrix Q i j x *ᵥ Pi.basisFun ℝ (Fin 3) 0)
      (rotationMatrix Q i j x *ᵥ Pi.basisFun ℝ (Fin 3) 1) =
        rotationMatrix Q i j x *ᵥ Pi.basisFun ℝ (Fin 3) 2
    rw [rotationMatrix_mulVec, rotationMatrix_mulVec, rotationMatrix_mulVec]
    rw [← rankThreeCoordChange_cross Q i j x hi hj,
      basis_cross_zero_one]
  have hnorm : (c 2) ⬝ᵥ (c 2) = 1 := by
    have h := rankThreeCoordChange_dot Q i j x hi hj
      (Pi.basisFun ℝ (Fin 3) 2) (Pi.basisFun ℝ (Fin 3) 2)
    change (rotationMatrix Q i j x *ᵥ Pi.basisFun ℝ (Fin 3) 2) ⬝ᵥ
      (rotationMatrix Q i j x *ᵥ Pi.basisFun ℝ (Fin 3) 2) = 1
    simpa [rotationMatrix, dotProduct, Pi.basisFun_apply, Pi.single_apply,
      Fin.sum_univ_succ] using h
  calc
    R.det = Rᵀ.det := (Matrix.det_transpose R).symm
    _ = Matrix.det ![c 0, c 1, c 2] := by rw [hcols]
    _ = (c 0) ⬝ᵥ crossProduct (c 1) (c 2) :=
      (triple_product_eq_det _ _ _).symm
    _ = (c 2) ⬝ᵥ crossProduct (c 0) (c 1) := by
      rw [triple_product_permutation, triple_product_permutation]
    _ = (c 2) ⬝ᵥ (c 2) := by rw [hcross]
    _ = 1 := hnorm

theorem rotationMatrix_specialOrthogonal (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    rotationMatrix Q i j x ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨(Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr
      (rotationMatrix_rows_orthogonal Q i j x hi hj),
    rotationMatrix_det_one Q i j x hi hj⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrientation
