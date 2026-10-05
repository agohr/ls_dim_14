import QuaternionicSymmetry.QuaternionicAction
import QuaternionicSymmetry.CompactSymplecticHaar
import QuaternionicSymmetry.OrbitalSourceConventions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The standard quaternionic structure on complex coordinates with grouped
indices. All operators are on the actual real inner-product space underlying
`EuclideanSpace ℂ (Fin n ⊕ Fin n)`. -/

namespace QuaternionicSymmetry.QuaternionicMatrixModel

open Matrix CompactSymplecticHaar

noncomputable section

abbrev V (n : ℕ) := EuclideanSpace ℂ (Fin n ⊕ Fin n)

/-- Complex multiplication by `i` as a real-linear isometry. -/
def standardI (n : ℕ) : V n ≃ₗᵢ[ℝ] V n where
  toFun v := Complex.I • v
  invFun v := -Complex.I • v
  map_add' v w := by simp [smul_add]
  map_smul' r v := by exact smul_comm _ _ _
  left_inv v := by simp only [smul_smul]; norm_num
  right_inv v := by simp only [smul_smul]; norm_num
  norm_map' v := by
    change ‖Complex.I • v‖ = ‖v‖
    rw [norm_smul, Complex.norm_I, one_mul]

def swapSummands (n : ℕ) : (Fin n ⊕ Fin n) ≃ (Fin n ⊕ Fin n) where
  toFun := Sum.swap
  invFun := Sum.swap
  left_inv := by intro i; cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

/-- Conjugation on each coordinate. -/
def conjugate (n : ℕ) : V n ≃ₗᵢ[ℝ] V n :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => Complex.conjLIE)

/-- Quaternionic `j`: swap the two `n`-blocks, conjugate, and change the
sign on the second block. -/
def standardJ (n : ℕ) : V n ≃ₗᵢ[ℝ] V n :=
  (conjugate n).trans ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ
    (swapSummands n)).trans
      (LinearIsometryEquiv.piLpCongrRight 2 (fun i =>
        match i with
        | Sum.inl _ => LinearIsometryEquiv.refl ℝ ℂ
        | Sum.inr _ => LinearIsometryEquiv.neg ℝ (E := ℂ))))

theorem standardI_apply (n : ℕ) (v : V n) : standardI n v = Complex.I • v := rfl

theorem standardJ_apply_inl (n : ℕ) (v : V n) (i : Fin n) :
    standardJ n v (Sum.inl i) = star (v (Sum.inr i)) := by
  simp [standardJ, conjugate, swapSummands, Complex.conjLIE_apply]

theorem standardJ_apply_inr (n : ℕ) (v : V n) (i : Fin n) :
    standardJ n v (Sum.inr i) = -star (v (Sum.inl i)) := by
  simp [standardJ, conjugate, swapSummands, Complex.conjLIE_apply]

/-- Coordinate identity used by the spectral matrix construction. -/
theorem standardJ_matrix_action (n : ℕ) (v : V n) :
    (standardJ n v).ofLp =
      CompactSymplecticHaar.standardJ n *ᵥ (fun k => star (v k)) := by
  funext k
  cases k with
  | inl i =>
      simp [standardJ_apply_inl, CompactSymplecticHaar.standardJ,
        Matrix.fromBlocks_mulVec]
  | inr i =>
      simp [standardJ_apply_inr, CompactSymplecticHaar.standardJ,
        Matrix.fromBlocks_mulVec, Matrix.neg_mulVec]

def standardQuaternionicStructure (n : ℕ) : QuaternionicStructure (V n) where
  I := standardI n
  J := standardJ n
  I_sq v := by
    ext (i | i) <;> simp [standardI_apply, smul_smul]
  J_sq v := by
    ext (i | i) <;>
      simp [standardJ_apply_inl, standardJ_apply_inr]
  I_J_anti v := by
    ext (i | i) <;>
      simp [standardI_apply, standardJ_apply_inl, standardJ_apply_inr,
        smul_eq_mul]

theorem real_finrank_eq_four_mul (n : ℕ) :
    Module.finrank ℝ (V n) = 4 * n := by
  calc
    Module.finrank ℝ (V n) = Module.finrank ℝ ℂ * Module.finrank ℂ (V n) :=
      (Module.finrank_mul_finrank ℝ ℂ (V n)).symm
    _ = 4 * n := by
      rw [Complex.finrank_real_complex, finrank_euclideanSpace]
      simp only [Fintype.card_sum, Fintype.card_fin]
      ring

theorem standardQuaternionicDimension (n : ℕ) :
    (standardQuaternionicStructure n).quaternionicDimension = n := by
  have h := (standardQuaternionicStructure n).real_finrank
  rw [real_finrank_eq_four_mul] at h
  omega

/-- The Hermitian matrices whose anti-Hermitian counterparts lie in the
compact symplectic Lie algebra. -/
def HermitianAntiSelfDual {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) : Prop :=
  Bᴴ = B ∧
    (Complex.I • B)ᵀ * CompactSymplecticHaar.standardJ n +
      CompactSymplecticHaar.standardJ n * (Complex.I • B) = 0

/-- Complex matrix multiplication, considered as a real-linear action. -/
def realMatrixAction {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) : V n →ₗ[ℝ] V n :=
  (Matrix.toEuclideanLin A).restrictScalars ℝ

theorem realMatrixAction_apply {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (v : V n) :
    (realMatrixAction A v).ofLp = A *ᵥ v.ofLp :=
  rfl

theorem HermitianAntiSelfDual_skew {n : ℕ}
    {B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hB : HermitianAntiSelfDual B) :
    (Complex.I • B)ᴴ = -(Complex.I • B) := by
  rw [Matrix.conjTranspose_smul, hB.1]
  simp

theorem hermitianAntiSelfDual_iff_skew_symplectic {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    HermitianAntiSelfDual B ↔
      (Complex.I • B)ᴴ = -(Complex.I • B) ∧
        (Complex.I • B)ᵀ * CompactSymplecticHaar.standardJ n +
          CompactSymplecticHaar.standardJ n * (Complex.I • B) = 0 := by
  constructor
  · intro h
    exact ⟨HermitianAntiSelfDual_skew h, h.2⟩
  · rintro ⟨hskew, hsp⟩
    constructor
    · have h := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ =>
        Complex.I • M) hskew
      simpa [Matrix.conjTranspose_smul, smul_smul, smul_neg] using h
    · exact hsp

theorem realMatrixAction_commute_I {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (v : V n) :
    realMatrixAction A (standardI n v) = standardI n (realMatrixAction A v) := by
  ext i
  simp [realMatrixAction_apply, standardI_apply, Matrix.mulVec_smul]

theorem real_inner_eq_complex_re (n : ℕ) (v w : V n) :
    inner ℝ v w = (inner ℂ v w).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_eq_re_inner ℂ (v i) (w i)

theorem realMatrixAction_skew_of_conjTranspose {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : Aᴴ = -A) (v w : V n) :
    inner ℝ (realMatrixAction A v) w = -inner ℝ v (realMatrixAction A w) := by
  have hAdj : (Matrix.toEuclideanLin A).adjoint = -Matrix.toEuclideanLin A := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hA]
    exact map_neg (Matrix.toEuclideanLin :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ ≃ₗ[ℂ]
        V n →ₗ[ℂ] V n) A
  rw [real_inner_eq_complex_re n, real_inner_eq_complex_re n]
  change (inner ℂ ((Matrix.toEuclideanLin A) v) w).re =
    -(inner ℂ v ((Matrix.toEuclideanLin A) w)).re
  rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A) v w,
    hAdj]
  simp

theorem skewSymplectic_commutes_J_matrix {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : Aᴴ = -A)
    (hSp : Aᵀ * CompactSymplecticHaar.standardJ n +
      CompactSymplecticHaar.standardJ n * A = 0) :
    A * CompactSymplecticHaar.standardJ n =
      CompactSymplecticHaar.standardJ n * A.map star := by
  let J := CompactSymplecticHaar.standardJ n
  have hstar : A.map star = -Aᵀ := by
    rw [← Matrix.conjTranspose_transpose, hA]
    rfl
  rw [hstar]
  have hJ : J * J = -1 := CompactSymplecticHaar.standardJ_sq n
  have h : A * J + J * Aᵀ = 0 := by
    have h' := congrArg (fun X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ =>
      J * X * J) hSp
    change J * (Aᵀ * J + J * A) * J = J * 0 * J at h'
    simp only [mul_zero, zero_mul] at h'
    simp only [mul_add, add_mul, mul_assoc] at h'
    rw [hJ] at h'
    simp only [mul_neg, mul_one] at h'
    rw [← mul_assoc J J (A * J), hJ] at h'
    have hneg : -(A * J + J * Aᵀ) = 0 := by
      calc
        _ = -(J * Aᵀ) + - (A * J) := by abel
        _ = 0 := by simpa only [neg_mul, one_mul] using h'
    exact neg_eq_zero.mp hneg
  simpa only [mul_neg] using eq_neg_of_add_eq_zero_left h

theorem realMatrixAction_commute_J {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : Aᴴ = -A)
    (hSp : Aᵀ * CompactSymplecticHaar.standardJ n +
      CompactSymplecticHaar.standardJ n * A = 0)
    (v : V n) :
    realMatrixAction A (standardJ n v) = standardJ n (realMatrixAction A v) := by
  let J := CompactSymplecticHaar.standardJ n
  let u : Fin n ⊕ Fin n → ℂ := v.ofLp
  let c : Fin n ⊕ Fin n → ℂ := fun k => star (u k)
  have hstarvec : A.map star *ᵥ c =
      fun k => star ((A *ᵥ u) k) := by
    funext k
    exact (RingHom.map_mulVec (starRingEnd ℂ) A u k).symm
  have hmat := skewSymplectic_commutes_J_matrix A hA hSp
  ext k
  have hleft := congrFun (realMatrixAction_apply A (standardJ n v)) k
  have hright := congrFun (standardJ_matrix_action n (realMatrixAction A v)) k
  rw [realMatrixAction_apply A v] at hright
  rw [standardJ_matrix_action n v] at hleft
  calc
    (realMatrixAction A (standardJ n v)) k = (A *ᵥ (J *ᵥ c)) k := hleft
    _ = ((A * J) *ᵥ c) k := by rw [Matrix.mulVec_mulVec]
    _ = ((J * A.map star) *ᵥ c) k := by rw [hmat]
    _ = (J *ᵥ (A.map star *ᵥ c)) k := by rw [Matrix.mulVec_mulVec]
    _ = (standardJ n (realMatrixAction A v)) k := by rw [hstarvec]; exact hright.symm

theorem HermitianAntiSelfDual_mem_skewCentralizer {n : ℕ}
    {B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hB : HermitianAntiSelfDual B) :
    realMatrixAction (Complex.I • B) ∈
      (standardQuaternionicStructure n).skewCentralizer := by
  change (∀ v w : V n,
      inner ℝ (realMatrixAction (Complex.I • B) v) w =
        -inner ℝ v (realMatrixAction (Complex.I • B) w)) ∧
    (∀ v : V n, realMatrixAction (Complex.I • B) (standardI n v) =
      standardI n (realMatrixAction (Complex.I • B) v)) ∧
    (∀ v : V n, realMatrixAction (Complex.I • B) (standardJ n v) =
      standardJ n (realMatrixAction (Complex.I • B) v))
  exact ⟨realMatrixAction_skew_of_conjTranspose _ (HermitianAntiSelfDual_skew hB),
    realMatrixAction_commute_I _,
    realMatrixAction_commute_J _ (HermitianAntiSelfDual_skew hB) hB.2⟩

/-- The source's Hermitian anti-self-dual diagonalizable matrices form a
real vector space, so every real linear combination stays in the spectral
class. -/
def hermitianAntiSelfDualSubmodule (n : ℕ) :
    Submodule ℝ (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) where
  carrier := {B | HermitianAntiSelfDual B}
  zero_mem' := by
    simp [HermitianAntiSelfDual]
  add_mem' := by
    intro B C hB hC
    rcases hB with ⟨hBh,hBs⟩
    rcases hC with ⟨hCh,hCs⟩
    constructor
    · simp [Matrix.conjTranspose_add, hBh, hCh]
    · simp only [smul_add, Matrix.transpose_add, add_mul, mul_add]
      calc
        (Complex.I • B)ᵀ * CompactSymplecticHaar.standardJ n +
            (Complex.I • C)ᵀ * CompactSymplecticHaar.standardJ n +
            (CompactSymplecticHaar.standardJ n * (Complex.I • B) +
              CompactSymplecticHaar.standardJ n * (Complex.I • C)) =
          ((Complex.I • B)ᵀ * CompactSymplecticHaar.standardJ n +
            CompactSymplecticHaar.standardJ n * (Complex.I • B)) +
          ((Complex.I • C)ᵀ * CompactSymplecticHaar.standardJ n +
            CompactSymplecticHaar.standardJ n * (Complex.I • C)) := by abel
        _ = 0 := by rw [hBs, hCs]; simp
  smul_mem' := by
    intro r B hB
    rcases hB with ⟨hBh,hBs⟩
    constructor
    · simp [Matrix.conjTranspose_smul, hBh]
    · have h : Complex.I • (r • B) = r • (Complex.I • B) := by
        ext i j
        simp [Matrix.smul_apply, mul_comm, mul_left_comm]
      rw [h, Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm]
      simp only [← smul_add, hBs, smul_zero]

/-- A unitary matrix preserves the standard alternating form exactly when
it commutes with the standard quaternionic anti-linear structure. -/
theorem unitary_mem_stabilizer_iff_commutes_J (n : ℕ)
    (U : Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ) :
    U ∈ stabilizer (CompactSymplecticHaar.standardJ n) ↔
      (U.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) *
        CompactSymplecticHaar.standardJ n =
      CompactSymplecticHaar.standardJ n * U.1.map star := by
  let J := CompactSymplecticHaar.standardJ n
  have hR : U.1ᵀ * U.1.map star = 1 := by
    have hu := (Matrix.mem_unitaryGroup_iff').mp U.2
    rw [Matrix.star_eq_conjTranspose] at hu
    have ht := congrArg Matrix.transpose hu
    simpa only [Matrix.transpose_mul, Matrix.conjTranspose_transpose,
      Matrix.transpose_one] using ht
  have hL : U.1.map star * U.1ᵀ = 1 := by
    have hu := (Matrix.mem_unitaryGroup_iff).mp U.2
    rw [Matrix.star_eq_conjTranspose] at hu
    have ht := congrArg Matrix.transpose hu
    simpa only [Matrix.transpose_mul, Matrix.conjTranspose_transpose,
      Matrix.transpose_one] using ht
  change U.1ᵀ * J * U.1 = J ↔ U.1 * J = J * U.1.map star
  constructor
  · intro hp
    have hpr := (OrbitalSourceConventions.transpose_preservation_iff J U.1
      (CompactSymplecticHaar.standardJ_sq n)).mp hp
    calc
      U.1 * J = (U.1 * J) * (U.1ᵀ * U.1.map star) := by rw [hR, mul_one]
      _ = (U.1 * J * U.1ᵀ) * U.1.map star := by simp only [mul_assoc]
      _ = J * U.1.map star := by rw [hpr]
  · intro hc
    apply (OrbitalSourceConventions.transpose_preservation_iff J U.1
      (CompactSymplecticHaar.standardJ_sq n)).mpr
    calc
      U.1 * J * U.1ᵀ = (J * U.1.map star) * U.1ᵀ := by rw [hc]
      _ = J := by rw [mul_assoc, hL, mul_one]

theorem matrix_commutes_J_iff_vector_action (n : ℕ)
    (U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    U * CompactSymplecticHaar.standardJ n =
        CompactSymplecticHaar.standardJ n * U.map star ↔
      ∀ v : Fin n ⊕ Fin n → ℂ,
        U *ᵥ (CompactSymplecticHaar.standardJ n *ᵥ (fun k => star (v k))) =
          CompactSymplecticHaar.standardJ n *ᵥ
            (fun k => star ((U *ᵥ v) k)) := by
  let J := CompactSymplecticHaar.standardJ n
  have hstar (v : Fin n ⊕ Fin n → ℂ) :
      U.map star *ᵥ (fun k => star (v k)) =
        fun k => star ((U *ᵥ v) k) := by
    funext k
    exact (RingHom.map_mulVec (starRingEnd ℂ) U v k).symm
  constructor
  · intro h v
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hstar]
  · intro h
    apply (Matrix.ext_iff_mulVec).2
    intro c
    let v : Fin n ⊕ Fin n → ℂ := fun k => star (c k)
    have hv := h v
    rw [Matrix.mulVec_mulVec] at hv
    rw [← hstar v, Matrix.mulVec_mulVec] at hv
    simpa only [v, star_star] using hv

theorem unitary_mem_stabilizer_iff_vector_action (n : ℕ)
    (U : Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ) :
    U ∈ stabilizer (CompactSymplecticHaar.standardJ n) ↔
      ∀ v : Fin n ⊕ Fin n → ℂ,
        (U.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) *ᵥ
            (CompactSymplecticHaar.standardJ n *ᵥ (fun k => star (v k))) =
          CompactSymplecticHaar.standardJ n *ᵥ
            (fun k => star ((U.1 *ᵥ v) k)) :=
  (unitary_mem_stabilizer_iff_commutes_J n U).trans
    (matrix_commutes_J_iff_vector_action n U.1)

end
end QuaternionicSymmetry.QuaternionicMatrixModel
