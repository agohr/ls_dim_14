import QuaternionicSymmetry.QuaternionicEigenbasisCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Explicit orthogonal projection onto a quaternionic line, including its
smooth dependence on a generating vector. These formulas support local
orthonormal frames of quaternionic invariant tangent subbundles. -/
namespace QuaternionicSymmetry.QuaternionicLineProjection
open QuaternionicStructure
open scoped BigOperators ContDiff
noncomputable section
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (Q : QuaternionicStructure E)

def projection (v : E) : E →L[ℝ] E :=
  ∑ k : Fin 4, InnerProductSpace.rankOne ℝ (Q.frame v k) (Q.frame v k)

@[simp] theorem projection_apply (v w : E) :
    projection Q v w = ∑ k : Fin 4, inner ℝ (Q.frame v k) w • Q.frame v k := by
  simp [projection]

theorem projection_I (v w : E) : projection Q v (Q.I w) = Q.I (projection Q v w) := by
  simp only [projection_apply, map_sum, map_smul]
  have hi (k : Fin 4) : inner ℝ (Q.frame v k) (Q.I w) =
      -inner ℝ (Q.I (Q.frame v k)) w := by rw [Q.I_skew]; simp
  simp [hi, I_frame, Fin.sum_univ_four]
  abel

theorem projection_J (v w : E) : projection Q v (Q.J w) = Q.J (projection Q v w) := by
  simp only [projection_apply, map_sum, map_smul]
  have hi (k : Fin 4) : inner ℝ (Q.frame v k) (Q.J w) =
      -inner ℝ (Q.J (Q.frame v k)) w := by rw [Q.J_skew]; simp
  simp [hi, J_frame, Fin.sum_univ_four]
  abel

theorem projection_frame (v : E) (hv : ‖v‖ = 1) (k : Fin 4) :
    projection Q v (Q.frame v k) = Q.frame v k := by
  simp [projection_apply, Q.frame_gram, hv]

theorem projection_inner (v w z : E) :
    inner ℝ (projection Q v w) z = inner ℝ w (projection Q v z) := by
  simp only [projection_apply, inner_sum, sum_inner, real_inner_smul_left,
    real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_comm w (Q.frame v k), mul_comm]

theorem residual_orthogonal (v : E) (hv : ‖v‖ = 1) (w : E) (k : Fin 4) :
    inner ℝ (Q.frame v k) (w - projection Q v w) = 0 := by
  rw [inner_sub_right, ← projection_inner, projection_frame Q v hv]
  simp

theorem projection_eq_zero (v w : E)
    (h : ∀ k, inner ℝ (Q.frame v k) w = 0) : projection Q v w = 0 := by
  simp [projection_apply, h]

theorem frame_smul (a : ℝ) (v : E) (k : Fin 4) :
    Q.frame (a • v) k = a • Q.frame v k := by
  fin_cases k <;> simp [QuaternionicStructure.frame]

theorem frame_contDiff (k : Fin 4) : ContDiff ℝ ∞ (fun v : E => Q.frame v k) := by
  fin_cases k
  · exact contDiff_id
  · exact Q.I.toContinuousLinearEquiv.contDiff
  · exact Q.J.toContinuousLinearEquiv.contDiff
  · exact Q.K.toContinuousLinearEquiv.contDiff

theorem projection_contDiff : ContDiff ℝ ∞ (projection Q) := by
  unfold projection
  apply ContDiff.sum
  intro k _
  exact (InnerProductSpace.rankOne ℝ).isBoundedBilinearMap.contDiff.comp
    ((frame_contDiff Q k).prodMk (frame_contDiff Q k))

def normalize (v : E) : E := ‖v‖⁻¹ • v

theorem normalize_norm (v : E) (hv : v ≠ 0) : ‖normalize v‖ = 1 := by
  simp [normalize, norm_smul, hv]

theorem normalize_contDiffAt {v : E} (hv : v ≠ 0) : ContDiffAt ℝ ∞ normalize v := by
  exact ((contDiffAt_norm ℝ hv).inv (norm_ne_zero_iff.mpr hv)).smul contDiffAt_id

theorem projection_mem (W : Submodule ℝ E) (v w : E)
    (hI : ∀ z ∈ W, Q.I z ∈ W) (hJ : ∀ z ∈ W, Q.J z ∈ W) (hv : v ∈ W) :
    projection Q v w ∈ W := by
  rw [projection_apply]
  apply W.sum_mem
  intro k _
  apply W.smul_mem
  fin_cases k
  · exact hv
  · exact hI v hv
  · exact hJ v hv
  · exact hI _ (hJ v hv)

theorem residual_mem_orthogonal (v : E) (hv : ‖v‖ = 1) (w : E) :
    w - projection Q v w ∈ (Q.frameSpan v).orthogonal := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k,rfl⟩ := hz
    exact residual_orthogonal Q v hv w k
  | zero => simp
  | add z z' _ _ hz hz' => simp only [inner_add_left,hz,hz',zero_add]
  | smul c z _ hz => simp only [inner_smul_left,hz,mul_zero]

end
end QuaternionicSymmetry.QuaternionicLineProjection
