import QuaternionicSymmetry.OrbitalComplexEigenframe
import QuaternionicSymmetry.OrbitalDiagonalSpectra

/-! Convert quaternionic real skew-centralizer eigenframes into actual
unitary symplectic diagonalizations. -/

namespace QuaternionicSymmetry.OrbitalSymplecticSpectral

open Matrix QuaternionicMatrixModel QuaternionicStructure
open OrbitalComplexEigenframe CompactSymplecticHaar OrbitalDiagonalSpectra

noncomputable section

theorem realMatrixAction_i_eigen_iff {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (v : V n) (lam : ℝ) :
    realMatrixAction (Complex.I • B) v = lam • standardI n v ↔
      Matrix.toEuclideanLin B v = (lam : ℂ) • v := by
  constructor
  · intro h
    change Matrix.toEuclideanLin (Complex.I • B) v =
      (lam : ℝ) • (Complex.I • v) at h
    rw [map_smul] at h
    change Complex.I • (Matrix.toEuclideanLin B v) =
      (lam : ℝ) • (Complex.I • v) at h
    have hscalar : (lam : ℝ) • (Complex.I • v) =
        Complex.I • ((lam : ℂ) • v) := by
      change (lam : ℂ) • (Complex.I • v) = _
      exact smul_comm _ _ _
    rw [hscalar] at h
    have h' : Complex.I • (Matrix.toEuclideanLin B v) =
        Complex.I • ((lam : ℂ) • v) := h
    exact (smul_right_injective (V n) Complex.I_ne_zero) h'
  · intro h
    change Matrix.toEuclideanLin (Complex.I • B) v =
      (lam : ℝ) • (Complex.I • v)
    rw [map_smul]
    change Complex.I • (Matrix.toEuclideanLin B v) =
      (lam : ℝ) • (Complex.I • v)
    rw [h]
    change Complex.I • ((lam : ℂ) • v) =
      (lam : ℂ) • (Complex.I • v)
    exact smul_comm _ _ _

theorem pairedVectors_eigen {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : realMatrixAction (Complex.I • B) ∈
      (standardQuaternionicStructure n).skewCentralizer)
    (vals : Fin n → ℝ) (v : Fin n → V n)
    (heig : ∀ j, realMatrixAction (Complex.I • B) (v j) =
      vals j • (standardQuaternionicStructure n).I (v j))
    (p : Fin n ⊕ Fin n) :
    Matrix.toEuclideanLin B (pairedVectors n v p) =
      ((Sum.elim vals (fun j => -vals j) p : ℝ) : ℂ) •
        pairedVectors n v p := by
  cases p with
  | inl j =>
      simpa only [pairedVectors] using
        (realMatrixAction_i_eigen_iff B (v j) (vals j)).mp (heig j)
  | inr j =>
      have hj := (standardQuaternionicStructure n).eigenline_action_J
        (realMatrixAction (Complex.I • B)) hA (heig j)
      change realMatrixAction (Complex.I • B) (standardJ n (v j)) =
        (-vals j) • standardI n (standardJ n (v j)) at hj
      have hB := (realMatrixAction_i_eigen_iff B
        (standardJ n (v j)) (-vals j)).mp hj
      simpa only [pairedVectors, map_neg, smul_neg] using congrArg Neg.neg hB

theorem pairedVectors_mulVec_eigen {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : realMatrixAction (Complex.I • B) ∈
      (standardQuaternionicStructure n).skewCentralizer)
    (vals : Fin n → ℝ) (v : Fin n → V n)
    (heig : ∀ j, realMatrixAction (Complex.I • B) (v j) =
      vals j • (standardQuaternionicStructure n).I (v j))
    (p : Fin n ⊕ Fin n) :
    B *ᵥ (pairedVectors n v p).ofLp =
      ((Sum.elim vals (fun j => -vals j) p : ℝ) : ℂ) •
        (pairedVectors n v p).ofLp := by
  have h := congrArg WithLp.ofLp (pairedVectors_eigen B hA vals v heig p)
  change (realMatrixAction B (pairedVectors n v p)).ofLp = _ at h
  rw [realMatrixAction_apply] at h
  simpa using h

theorem pairedMatrix_diagonalizes {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : realMatrixAction (Complex.I • B) ∈
      (standardQuaternionicStructure n).skewCentralizer)
    (vals : Fin n → ℝ) (v : Fin n → V n)
    (heig : ∀ j, realMatrixAction (Complex.I • B) (v j) =
      vals j • (standardQuaternionicStructure n).I (v j))
    (c : OrthonormalBasis (Fin n ⊕ Fin n) ℂ (V n))
    (hc : ∀ p, c p = pairedVectors n v p) :
    B * pairedMatrix n c = pairedMatrix n c * hermitianDiagonal vals := by
  ext i j
  have hj := congrFun (pairedVectors_mulVec_eigen B hA vals v heig j) i
  calc
    (B * pairedMatrix n c) i j =
        (B *ᵥ (pairedVectors n v j).ofLp) i := by
      simp only [Matrix.mul_apply, pairedMatrix_apply, hc,
        Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    _ = ((Sum.elim vals (fun a => -vals a) j : ℝ) : ℂ) *
        pairedVectors n v j i := by simpa only [Pi.smul_apply, smul_eq_mul] using hj
    _ = (pairedMatrix n c * hermitianDiagonal vals) i j := by
      simp [Matrix.mul_apply, hermitianDiagonal, Matrix.diagonal_apply,
        pairedMatrix_apply, hc]
      cases j <;> simp <;> ring

/-- Every Hermitian anti-self-dual matrix has an actual compact symplectic
diagonalization with paired real eigenvalues. -/
theorem exists_symplectic_diagonalization {n : ℕ}
    {B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hB : HermitianAntiSelfDual B) :
    ∃ (x : Fin n → ℝ) (u : CompactSymplecticHaar.Group n),
      B = conjugate (CompactSymplecticHaar.standardJ n) u
        (hermitianDiagonal x) := by
  have hA := HermitianAntiSelfDual_mem_skewCentralizer hB
  have hEig :
      ∃ (vals : Fin n → ℝ) (v : Fin n → V n)
        (b : OrthonormalBasis (Fin n × Fin 4) ℝ (V n)),
        (∀ p, b p = (standardQuaternionicStructure n).frame (v p.1) p.2) ∧
        (∀ j, realMatrixAction (Complex.I • B) (v j) =
          vals j • (standardQuaternionicStructure n).I (v j)) := by
    have hraw :=
      (standardQuaternionicStructure n).exists_eigenOrthonormalBasis_fin
        (realMatrixAction (Complex.I • B)) hA
    rw [standardQuaternionicDimension n] at hraw
    exact hraw
  obtain ⟨vals, v, b, hb, heig⟩ := hEig
  obtain ⟨c, hc⟩ := exists_pairedOrthonormalBasis n v b hb
  let U := pairedMatrix n c
  have hU : U ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ :=
    pairedMatrix_unitary n c
  have hSp : (⟨U, hU⟩ : Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ) ∈
      CompactSymplecticHaar.Group n := pairedMatrix_mem_group n v c hc
  let u : CompactSymplecticHaar.Group n := ⟨⟨U, hU⟩, hSp⟩
  have hdiag : B * U = U * hermitianDiagonal vals :=
    pairedMatrix_diagonalizes B hA vals v heig c hc
  have hunit : U * Uᴴ = 1 := by
    exact (Matrix.mem_unitaryGroup_iff).mp hU
  refine ⟨vals, u, ?_⟩
  change B = U * hermitianDiagonal vals * Uᴴ
  calc
    B = B * (U * Uᴴ) := by rw [hunit, mul_one]
    _ = (B * U) * Uᴴ := by rw [mul_assoc]
    _ = (U * hermitianDiagonal vals) * Uᴴ := by rw [hdiag]

end
end QuaternionicSymmetry.OrbitalSymplecticSpectral
