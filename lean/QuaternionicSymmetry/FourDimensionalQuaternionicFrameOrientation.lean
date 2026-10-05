import QuaternionicSymmetry.FourDimensionalQuaternionicHodgeFrame

/-! The explicit real 4×4 transition matrix of two unit quaternionic frames.
Its determinant is a square, providing the orientation sign without invoking
an unproved connectedness argument. -/
namespace QuaternionicSymmetry.FourDimensionalQuaternionicFrameOrientation

open FourDimensionalQuaternionicHodgeFrame
noncomputable section

def quaternionicFrameMatrix (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a, -b, -c, -d;
     b, a, d, -c;
     c, -d, a, b;
     d, c, -b, a]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def frameTransitionMatrix (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v w : V)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : Matrix (Fin 4) (Fin 4) ℝ :=
  (frameBasis Q hdim v hv).toBasis.toMatrix (frameBasis Q hdim w hw).toBasis

theorem frameTransitionMatrix_apply (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v w : V)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (i j : Fin 4) :
    frameTransitionMatrix Q hdim v w hv hw i j =
      inner ℝ (Q.frame v i) (Q.frame w j) := by
  rw [frameTransitionMatrix, Module.Basis.toMatrix_apply]
  change (frameBasis Q hdim v hv).repr (frameBasis Q hdim w hw j) i = _
  rw [OrthonormalBasis.repr_apply_apply, frameBasis_apply, frameBasis_apply]

theorem frameTransitionMatrix_eq_quaternionic (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v w : V)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    frameTransitionMatrix Q hdim v w hv hw =
      quaternionicFrameMatrix
        (inner ℝ v w) (inner ℝ (Q.I v) w)
        (inner ℝ (Q.J v) w) (inner ℝ (Q.K v) w) := by
  have hI (i : Fin 4) :
      inner ℝ (Q.frame v i) (Q.I w) =
        -inner ℝ (Q.I (Q.frame v i)) w := by
    have h := Q.I_skew (Q.frame v i) w
    linarith
  have hJ (i : Fin 4) :
      inner ℝ (Q.frame v i) (Q.J w) =
        -inner ℝ (Q.J (Q.frame v i)) w := by
    have h := Q.J_skew (Q.frame v i) w
    linarith
  have hK (i : Fin 4) :
      inner ℝ (Q.frame v i) (Q.K w) =
        -inner ℝ (Q.K (Q.frame v i)) w := by
    have h := Q.K_skew (Q.frame v i) w
    linarith
  ext i j
  rw [frameTransitionMatrix_apply]
  fin_cases j
  · fin_cases i <;>
      simp [quaternionicFrameMatrix, QuaternionicStructure.frame]
  · change inner ℝ (Q.frame v i) (Q.I w) = _
    rw [hI i]
    fin_cases i <;>
      simp [quaternionicFrameMatrix, Q.I_frame_zero,
        Q.I_frame_one, Q.I_frame_two, Q.I_frame_three,
        QuaternionicStructure.frame] <;>
      simp [Q.I_sq, Q.J_sq, Q.J_I_anti, map_neg]
  · change inner ℝ (Q.frame v i) (Q.J w) = _
    rw [hJ i]
    fin_cases i <;>
      simp [quaternionicFrameMatrix, Q.J_frame_zero,
        Q.J_frame_one, Q.J_frame_two, Q.J_frame_three,
        QuaternionicStructure.frame] <;>
      simp [Q.I_sq, Q.J_sq, Q.J_I_anti, map_neg]
  · change inner ℝ (Q.frame v i) (Q.K w) = _
    rw [hK i]
    fin_cases i <;>
      simp [quaternionicFrameMatrix, Q.K_frame_zero,
        Q.K_frame_one, Q.K_frame_two, Q.K_frame_three,
        QuaternionicStructure.frame] <;>
      simp [Q.I_sq, Q.J_sq, Q.J_I_anti, map_neg]

private theorem vec3_two (x y z : ℝ) : (![x, y, z] : Fin 3 → ℝ) 2 = z := by
  rfl

private theorem vec4_two (w x y z : ℝ) : (![w, x, y, z] : Fin 4 → ℝ) 2 = y := by
  rfl

private theorem vec4_three (w x y z : ℝ) : (![w, x, y, z] : Fin 4 → ℝ) 3 = z := by
  rfl

@[simp] private theorem cons3_two (x y z : ℝ) :
    Matrix.vecCons x (fun i => Matrix.vecCons y (fun _ => z) i) (2 : Fin 3) = z := by
  rfl

@[simp] private theorem cons4_two (w x y z : ℝ) :
    Matrix.vecCons w
      (fun i => Matrix.vecCons x (fun i => Matrix.vecCons y (fun _ => z) i) i)
      (2 : Fin 4) = y := by
  rfl

private theorem above00 : (0 : Fin 4).succAbove (0 : Fin 3) = 1 := by decide
private theorem above01 : (0 : Fin 4).succAbove (1 : Fin 3) = 2 := by decide
private theorem above02 : (0 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
private theorem above10 : (1 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide
private theorem above11 : (1 : Fin 4).succAbove (1 : Fin 3) = 2 := by decide
private theorem above12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
private theorem above20 : (2 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide
private theorem above21 : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
private theorem above22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
private theorem above30 : (3 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide
private theorem above31 : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
private theorem above32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
private theorem above3_00 : (0 : Fin 3).succAbove (0 : Fin 2) = 1 := by decide
private theorem above3_01 : (0 : Fin 3).succAbove (1 : Fin 2) = 2 := by decide
private theorem above3_10 : (1 : Fin 3).succAbove (0 : Fin 2) = 0 := by decide
private theorem above3_11 : (1 : Fin 3).succAbove (1 : Fin 2) = 2 := by decide
private theorem above3_20 : (2 : Fin 3).succAbove (0 : Fin 2) = 0 := by decide
private theorem above3_21 : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
private theorem cast3_two : (2 : Fin 3).castSucc = (2 : Fin 4) := by decide
private theorem cast2_one : (1 : Fin 2).castSucc = (1 : Fin 3) := by decide

set_option maxHeartbeats 2000000 in
theorem quaternionicFrameMatrix_det (a b c d : ℝ) :
    (quaternionicFrameMatrix a b c d).det =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 := by
  simp only [quaternionicFrameMatrix, Matrix.det_succ_row_zero,
    Matrix.det_fin_three, Fin.sum_univ_succ]
  norm_num [Matrix.submatrix_apply, Fin.ext_iff,
    above00, above01, above02, above10, above11, above12,
    above20, above21, above22, above30, above31, above32,
    above3_00, above3_01, above3_10, above3_11, above3_20, above3_21,
    cast3_two, cast2_one, vec3_two, vec4_two, vec4_three]
  ring

theorem frame_coordinates_unit (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v w : V)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    (inner ℝ v w) ^ 2 + (inner ℝ (Q.I v) w) ^ 2 +
      (inner ℝ (Q.J v) w) ^ 2 + (inner ℝ (Q.K v) w) ^ 2 = 1 := by
  have h := (frameBasis Q hdim v hv).sum_inner_mul_inner w w
  rw [real_inner_self_eq_norm_sq, hw] at h
  simp [Fin.sum_univ_succ, frameBasis_apply,
    QuaternionicStructure.frame, real_inner_comm] at h
  rw [← real_inner_comm w (Q.I v), ← real_inner_comm w (Q.J v),
    ← real_inner_comm w (Q.I (Q.J v))] at h
  simp only [QuaternionicStructure.K_apply]
  nlinarith [h]

theorem frameTransitionMatrix_det_one (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v w : V)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    (frameTransitionMatrix Q hdim v w hv hw).det = 1 := by
  rw [frameTransitionMatrix_eq_quaternionic, quaternionicFrameMatrix_det,
    frame_coordinates_unit Q hdim v w hv hw]
  norm_num

end
end QuaternionicSymmetry.FourDimensionalQuaternionicFrameOrientation
