import QuaternionicSymmetry.FourDimensionalBlockDeterminant
import QuaternionicSymmetry.FourDimensionalQuaternionicPointwiseOrientation
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrientation

/-! Four-dimensional adapted tangent transitions preserve the orientation
defined by the *local* quaternionic frames. This uses the actual orthogonal
adapted transition and its proved SO(3) action on the rank-three Q-plane. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFourOrientationTransitions

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourFormTransitions
open ManifoldQuaternionicRankThreeOrientation
open FourDimensionalQuaternionicHodgeFrame
open FourDimensionalQuaternionicPointwiseOrientation
open FourDimensionalBlockDeterminant
open VectorBundleFrameTransitions
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

private theorem norm_coordChange_one (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (v : E) (hv : ‖v‖ = 1) :
    ‖Q.frames.coordChange i j x v‖ = 1 := by
  have h := Q.transition_inner i j x hi hj v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hv] at h
  nlinarith [norm_nonneg (Q.frames.coordChange i j x v)]

def adaptedFrameMatrix (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (v : E) (hv : ‖v‖ = 1) : Matrix (Fin 4) (Fin 4) ℝ :=
  let w := Q.frames.coordChange i j x v
  let hw := norm_coordChange_one Q i j x hi hj v hv
  fun a b => inner ℝ
    ((frameBasis (Q.reduction.Q j) hdim w hw) a)
    (Q.frames.coordChange i j x
      ((frameBasis (Q.reduction.Q i) hdim v hv) b))

theorem adaptedFrameMatrix_first_column (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (v : E) (hv : ‖v‖ = 1) :
    adaptedFrameMatrix Q hdim i j x hi hj v hv 0 0 = 1 := by
  have hw := norm_coordChange_one Q i j x hi hj v hv
  simp [adaptedFrameMatrix, frameBasis_apply, QuaternionicStructure.frame,
    real_inner_self_eq_norm_sq, hw]

theorem adaptedFrameMatrix_first_row_tail (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (v : E) (hv : ‖v‖ = 1) (s : Fin 3) :
    adaptedFrameMatrix Q hdim i j x hi hj v hv 0 (Fin.succ s) = 0 := by
  have horth := (Q.reduction.Q i).frame_orthonormal v hv
  have hinner := orthonormal_iff_ite.mp horth 0 (Fin.succ s)
  have hne : (0 : Fin 4) ≠ Fin.succ s := by fin_cases s <;> decide
  rw [if_neg hne] at hinner
  simp only [adaptedFrameMatrix, frameBasis_apply]
  change inner ℝ (Q.frames.coordChange i j x v)
    (Q.frames.coordChange i j x
      ((Q.reduction.Q i).frame v (Fin.succ s))) = 0
  rw [Q.transition_inner i j x hi hj]
  exact hinner

theorem adaptedFrameMatrix_lower_right (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (v : E) (hv : ‖v‖ = 1) (t s : Fin 3) :
    adaptedFrameMatrix Q hdim i j x hi hj v hv
      (Fin.succ t) (Fin.succ s) = rotationMatrix Q i j x t s := by
  let w := Q.frames.coordChange i j x v
  have hw := norm_coordChange_one Q i j x hi hj v hv
  have horth := (Q.reduction.Q j).frame_orthonormal w hw
  have hinner (a b : Fin 4) :
      inner ℝ ((Q.reduction.Q j).frame w a)
        ((Q.reduction.Q j).frame w b) = if a = b then 1 else 0 :=
    orthonormal_iff_ite.mp horth a b
  simp only [adaptedFrameMatrix, frameBasis_apply]
  change inner ℝ ((Q.reduction.Q j).frame w (Fin.succ t))
    (Q.frames.coordChange i j x
      ((Q.reduction.Q i).frame v (Fin.succ s))) = _
  have hgen := generator_transition Q i j x hi hj s v
  simp only [ManifoldQuaternionicRankThreeOrthogonal.generator_apply_eq_frame] at hgen
  change Q.frames.coordChange i j x
      ((Q.reduction.Q i).frame v (Fin.succ s)) =
    ∑ a : Fin 3, rotationMatrix Q i j x a s •
      (Q.reduction.Q j).frame w (Fin.succ a) at hgen
  rw [hgen, inner_sum]
  simp only [real_inner_smul_right, hinner]
  simp [Finset.sum_ite_eq', eq_comm]

theorem adaptedFrameMatrix_det_one (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (v : E) (hv : ‖v‖ = 1) :
    (adaptedFrameMatrix Q hdim i j x hi hj v hv).det = 1 := by
  rw [det_eq_lower_right _ (rotationMatrix Q i j x)
    (adaptedFrameMatrix_first_column Q hdim i j x hi hj v hv)
    (adaptedFrameMatrix_first_row_tail Q hdim i j x hi hj v hv)
    (adaptedFrameMatrix_lower_right Q hdim i j x hi hj v hv)]
  exact rotationMatrix_det_one Q i j x hi hj

/-- The actual adapted tangent transition carries the pointwise orientation
of the source local quaternionic structure to that of the target structure.
This is an overlap transport statement, not yet a global oriented atlas. -/
theorem adaptedTransition_preserves_pointwiseOrientation
    (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    Orientation.map (Fin 4) (Q.frameTransition i j x hi hj).toLinearEquiv
      (pointwiseQuaternionicOrientation (Q.reduction.Q i) hdim) =
    pointwiseQuaternionicOrientation (Q.reduction.Q j) hdim := by
  obtain ⟨v, hv0⟩ := exists_ne (0 : E)
  let v' := NormedSpace.normalize v
  have hv : ‖v'‖ = 1 := NormedSpace.norm_normalize hv0
  let T := Q.frameTransition i j x hi hj
  let w := T v'
  have hw : ‖w‖ = 1 := norm_coordChange_one Q i j x hi hj v' hv
  let bi := frameBasis (Q.reduction.Q i) hdim v' hv
  let bj := frameBasis (Q.reduction.Q j) hdim w hw
  have hmatrix : bj.toBasis.toMatrix (bi.toBasis.map T.toLinearEquiv) =
      adaptedFrameMatrix Q hdim i j x hi hj v' hv := by
    ext a b
    rw [Module.Basis.toMatrix_apply]
    change bj.repr (T (bi b)) a = _
    rw [OrthonormalBasis.repr_apply_apply]
    rfl
  have hdet : bj.toBasis.det (bi.toBasis.map T.toLinearEquiv) = 1 := by
    rw [Module.Basis.det_apply, hmatrix]
    exact adaptedFrameMatrix_det_one Q hdim i j x hi hj v' hv
  have hor : (bi.toBasis.map T.toLinearEquiv).orientation =
      bj.toBasis.orientation := by
    symm
    apply (Module.Basis.orientation_eq_iff_det_pos bj.toBasis
      (bi.toBasis.map T.toLinearEquiv)).mpr
    rw [hdet]
    norm_num
  rw [bi.toBasis.orientation_map] at hor
  rw [← frame_has_pointwiseQuaternionicOrientation (Q.reduction.Q i) hdim v' hv,
    ← frame_has_pointwiseQuaternionicOrientation (Q.reduction.Q j) hdim w hw]
  exact hor

end
end QuaternionicSymmetry.ManifoldQuaternionicFourOrientationTransitions
