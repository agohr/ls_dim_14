import QuaternionicSymmetry.QuaternionicMatrixModel

/-! The symplectic transpose and projection of Hermitian contractions onto
the Hermitian symplectic Lie algebra, preserving their relevant trace pairing. -/

namespace QuaternionicSymmetry.SymplecticTraceProjection

open Matrix QuaternionicMatrixModel

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def symplecticTranspose (J : Matrix κ κ ℂ) :
    Matrix κ κ ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun B := -(J * Bᵀ * J)
  map_add' B C := by simp [Matrix.transpose_add, mul_add, add_mul, add_comm]
  map_smul' c B := by simp [Matrix.transpose_smul]

theorem symplecticTranspose_involutive (J : Matrix κ κ ℂ)
    (hJt : Jᵀ = -J) (hJsq : J * J = -1) (B : Matrix κ κ ℂ) :
    symplecticTranspose J (symplecticTranspose J B) = B := by
  change -(J * (-(J * Bᵀ * J))ᵀ * J) = B
  simp only [Matrix.transpose_neg, Matrix.transpose_mul,
    Matrix.transpose_transpose, hJt, mul_neg, neg_mul, neg_neg]
  calc
    _ = (J * J) * B * (J * J) := by simp only [mul_assoc]
    _ = B := by rw [hJsq]; simp

theorem trace_symplecticTranspose_pair (J : Matrix κ κ ℂ) (hJt : Jᵀ = -J)
    (B X : Matrix κ κ ℂ) :
    Matrix.trace (symplecticTranspose J B * X) =
      Matrix.trace (B * symplecticTranspose J X) := by
  change Matrix.trace (-(J * Bᵀ * J) * X) = Matrix.trace (B * -(J * Xᵀ * J))
  simp only [neg_mul, mul_neg, Matrix.trace_neg, neg_inj]
  rw [← Matrix.trace_transpose (B * (J * Xᵀ * J))]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hJt, mul_neg,
    neg_mul, neg_neg]
  rw [Matrix.mul_assoc (J * Bᵀ), Matrix.trace_mul_comm (J * Bᵀ)]
  simp only [mul_assoc]

def antiProjection (J : Matrix κ κ ℂ) (B : Matrix κ κ ℂ) : Matrix κ κ ℂ :=
  (1 / 2 : ℂ) • (B - symplecticTranspose J B)

theorem antiProjection_anti (J : Matrix κ κ ℂ)
    (hJt : Jᵀ = -J) (hJsq : J * J = -1) (B : Matrix κ κ ℂ) :
    symplecticTranspose J (antiProjection J B) = -antiProjection J B := by
  rw [antiProjection, map_smul, map_sub, symplecticTranspose_involutive J hJt hJsq]
  simp only [← smul_neg]
  congr 1
  abel

theorem trace_antiProjection (J : Matrix κ κ ℂ) (hJt : Jᵀ = -J)
    (B X : Matrix κ κ ℂ) (hX : symplecticTranspose J X = -X) :
    Matrix.trace (antiProjection J B * X) = Matrix.trace (B * X) := by
  simp only [antiProjection, Matrix.smul_mul, sub_mul, Matrix.trace_smul,
    Matrix.trace_sub, smul_eq_mul]
  rw [trace_symplecticTranspose_pair J hJt, hX, mul_neg, Matrix.trace_neg]
  ring

theorem symplecticTranspose_neg_iff (J : Matrix κ κ ℂ) (hJsq : J * J = -1)
    (X : Matrix κ κ ℂ) :
    symplecticTranspose J X = -X ↔ Xᵀ * J + J * X = 0 := by
  constructor
  · intro h
    have ht : J * Xᵀ * J = X := neg_inj.mp h
    have hh : -(Xᵀ * J) = J * X := by
      calc
        _ = J * (J * Xᵀ * J) := by rw [← mul_assoc, ← mul_assoc, hJsq]; simp
        _ = J * X := by rw [ht]
    rw [← hh]
    simp
  · intro h
    have ht : Xᵀ * J = -(J * X) := eq_neg_of_add_eq_zero_left h
    change -(J * Xᵀ * J) = -X
    congr 1
    rw [mul_assoc, ht, mul_neg, ← mul_assoc, hJsq]
    simp

theorem symplecticTranspose_conjTranspose (J : Matrix κ κ ℂ) (hJh : Jᴴ = -J)
    (B : Matrix κ κ ℂ) :
    (symplecticTranspose J B)ᴴ = symplecticTranspose J Bᴴ := by
  change (-(J * Bᵀ * J))ᴴ = -(J * (Bᴴ)ᵀ * J)
  simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hJh,
    Matrix.conjTranspose_transpose, Matrix.transpose_conjTranspose,
    mul_neg, neg_mul, neg_neg, mul_assoc]

theorem antiProjection_hermitian (J : Matrix κ κ ℂ) (hJh : Jᴴ = -J)
    (B : Matrix κ κ ℂ) (hB : Bᴴ = B) :
    (antiProjection J B)ᴴ = antiProjection J B := by
  simp only [antiProjection, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    symplecticTranspose_conjTranspose J hJh, hB]
  norm_num

theorem standardJ_conjTranspose (n : ℕ) :
    (CompactSymplecticHaar.standardJ n)ᴴ = -CompactSymplecticHaar.standardJ n := by
  simp [CompactSymplecticHaar.standardJ, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_neg]

theorem hermitianAntiSelfDual_iff {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    HermitianAntiSelfDual B ↔ Bᴴ = B ∧
      symplecticTranspose (CompactSymplecticHaar.standardJ n) B = -B := by
  rw [HermitianAntiSelfDual, symplecticTranspose_neg_iff _ (CompactSymplecticHaar.standardJ_sq n)]
  have h : (Complex.I • B)ᵀ * CompactSymplecticHaar.standardJ n +
      CompactSymplecticHaar.standardJ n * (Complex.I • B) =
      Complex.I • (Bᵀ * CompactSymplecticHaar.standardJ n +
        CompactSymplecticHaar.standardJ n * B) := by
    simp [Matrix.transpose_smul, smul_add]
  rw [h, smul_eq_zero]
  simp

/-- Every Hermitian contraction projects into the actual matrix spectral
class; no positivity or diagonalization is assumed of the contraction. -/
theorem antiProjection_HermitianAntiSelfDual {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (hB : Bᴴ = B) :
    HermitianAntiSelfDual (antiProjection (CompactSymplecticHaar.standardJ n) B) := by
  rw [hermitianAntiSelfDual_iff]
  exact ⟨antiProjection_hermitian _ (standardJ_conjTranspose n) B hB,
    antiProjection_anti _ (CompactSymplecticHaar.standardJ_transpose n)
      (CompactSymplecticHaar.standardJ_sq n) B⟩

theorem trace_antiProjection_of_HermitianAntiSelfDual {n : ℕ}
    (B X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hX : HermitianAntiSelfDual X) :
    Matrix.trace (antiProjection (CompactSymplecticHaar.standardJ n) B * X) =
      Matrix.trace (B * X) :=
  trace_antiProjection _ (CompactSymplecticHaar.standardJ_transpose n) B X
    ((hermitianAntiSelfDual_iff X).mp hX).2

theorem HermitianAntiSelfDual_conjugate {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hB : HermitianAntiSelfDual B) (g : CompactSymplecticHaar.Group n) :
    HermitianAntiSelfDual
      (CompactSymplecticHaar.conjugate (CompactSymplecticHaar.standardJ n) g B) := by
  let J := CompactSymplecticHaar.standardJ n
  let U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := g.1
  have huu : U * Uᴴ = 1 := g.1.2.2
  have huhu : Uᴴ * U = 1 := g.1.2.1
  have hleft : Uᵀ * J = J * Uᴴ := by
    calc
      _ = Uᵀ * J * (U * Uᴴ) := by rw [huu]; simp
      _ = (Uᵀ * J * U) * Uᴴ := by simp only [mul_assoc]
      _ = J * Uᴴ := by rw [g.2]
  have hinv : (Uᴴ)ᵀ * J * Uᴴ = J := (g⁻¹).2
  have hright : J * U = (Uᴴ)ᵀ * J := by
    calc
      _ = ((Uᴴ)ᵀ * J * Uᴴ) * U := by rw [hinv]
      _ = (Uᴴ)ᵀ * J * (Uᴴ * U) := by simp only [mul_assoc]
      _ = (Uᴴ)ᵀ * J := by rw [huhu]; simp
  rw [hermitianAntiSelfDual_iff,
    symplecticTranspose_neg_iff _ (CompactSymplecticHaar.standardJ_sq n)]
  constructor
  · simp [CompactSymplecticHaar.conjugate, Matrix.conjTranspose_mul, hB.1, mul_assoc]
  · have hb : Bᵀ * J + J * B = 0 :=
      (symplecticTranspose_neg_iff J (CompactSymplecticHaar.standardJ_sq n) B).mp
        ((hermitianAntiSelfDual_iff B).mp hB).2
    change (U * B * Uᴴ)ᵀ * J + J * (U * B * Uᴴ) = 0
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    calc
      _ = (Uᴴ)ᵀ * Bᵀ * (Uᵀ * J) + (J * U) * B * Uᴴ := by
        simp only [mul_assoc]
      _ = (Uᴴ)ᵀ * (Bᵀ * J + J * B) * Uᴴ := by
        rw [hleft, hright]
        noncomm_ring
      _ = 0 := by rw [hb]; simp

/-- An arbitrary Hermitian contraction and its symplectic projection give
the same scalar form at every compact symplectic frame. -/
theorem halfTrace_antiProjection {n : ℕ}
    (B X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hX : HermitianAntiSelfDual X) (g : CompactSymplecticHaar.Group n) :
    CompactSymplecticHaar.halfTrace (CompactSymplecticHaar.standardJ n)
      (antiProjection (CompactSymplecticHaar.standardJ n) B) X g =
    CompactSymplecticHaar.halfTrace (CompactSymplecticHaar.standardJ n) B X g := by
  have h := trace_antiProjection_of_HermitianAntiSelfDual B
    (CompactSymplecticHaar.conjugate (CompactSymplecticHaar.standardJ n) g X)
    (HermitianAntiSelfDual_conjugate X hX g)
  simpa only [CompactSymplecticHaar.halfTrace, CompactSymplecticHaar.conjugate,
    mul_assoc] using congrArg (fun z : ℂ => z.re / 2) h

end
end QuaternionicSymmetry.SymplecticTraceProjection
