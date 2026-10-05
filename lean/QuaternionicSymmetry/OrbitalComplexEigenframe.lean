import QuaternionicSymmetry.QuaternionicMatrixModel
import QuaternionicSymmetry.QuaternionicEigenbasisFinite
import Mathlib.Data.Complex.BigOperators

/-! Convert a real quaternionic four-frame into a complex orthonormal paired
frame. The second column of each pair is `-J v`, matching the grouped
symplectic matrix convention. -/

namespace QuaternionicSymmetry.OrbitalComplexEigenframe

open QuaternionicMatrixModel QuaternionicStructure

noncomputable section

def pairedVectors (n : ℕ) (v : Fin n → V n) :
    Fin n ⊕ Fin n → V n
  | Sum.inl j => v j
  | Sum.inr j => -standardJ n (v j)

theorem real_inner_eq_complex_re (n : ℕ) (u w : V n) :
    inner ℝ u w = (inner ℂ u w).re := by
  simp [PiLp.inner_apply, real_inner_eq_re_inner, Complex.re_sum]

theorem complex_inner_im_eq_real_I (n : ℕ) (u w : V n) :
    (inner ℂ u w).im = inner ℝ (Complex.I • u) w := by
  rw [real_inner_eq_complex_re]
  simp [inner_smul_left]

theorem pairedVectors_orthonormal (n : ℕ) (v : Fin n → V n)
    (b : OrthonormalBasis (Fin n × Fin 4) ℝ (V n))
    (hb : ∀ p, b p = (standardQuaternionicStructure n).frame (v p.1) p.2) :
    Orthonormal ℂ (pairedVectors n v) := by
  classical
  have hframe (j l : Fin n) (r s : Fin 4) :
      inner ℝ ((standardQuaternionicStructure n).frame (v j) r)
        ((standardQuaternionicStructure n).frame (v l) s) =
        if (j,r) = (l,s) then 1 else 0 := by
    simpa only [hb] using
      (orthonormal_iff_ite.mp b.orthonormal (j,r) (l,s))
  apply orthonormal_iff_ite.mpr
  intro p q
  apply Complex.ext
  · rw [← real_inner_eq_complex_re]
    cases p with
    | inl i => cases q with
      | inl j => simpa [pairedVectors, QuaternionicStructure.frame, apply_ite] using hframe i j 0 0
      | inr j => simpa [pairedVectors, QuaternionicStructure.frame] using hframe i j 0 2
    | inr i => cases q with
      | inl j => simpa [pairedVectors, QuaternionicStructure.frame] using hframe i j 2 0
      | inr j => simpa [pairedVectors, QuaternionicStructure.frame, apply_ite] using hframe i j 2 2
  · rw [complex_inner_im_eq_real_I]
    cases p with
    | inl i => cases q with
      | inl j => simpa [pairedVectors, QuaternionicStructure.frame,
          ← standardI_apply, apply_ite] using hframe i j 1 0
      | inr j => simpa [pairedVectors, QuaternionicStructure.frame,
          ← standardI_apply] using hframe i j 1 2
    | inr i => cases q with
      | inl j => simpa [pairedVectors, QuaternionicStructure.frame,
          ← standardI_apply, QuaternionicStructure.K_apply] using hframe i j 3 0
      | inr j => simpa [pairedVectors, QuaternionicStructure.frame,
          ← standardI_apply, QuaternionicStructure.K_apply, apply_ite] using hframe i j 3 2

theorem exists_pairedOrthonormalBasis (n : ℕ) (v : Fin n → V n)
    (b : OrthonormalBasis (Fin n × Fin 4) ℝ (V n))
    (hb : ∀ p, b p = (standardQuaternionicStructure n).frame (v p.1) p.2) :
    ∃ c : OrthonormalBasis (Fin n ⊕ Fin n) ℂ (V n),
      ∀ i, c i = pairedVectors n v i := by
  have hcard : Module.finrank ℂ (V n) = Fintype.card (Fin n ⊕ Fin n) := by
    simp [finrank_euclideanSpace, Fintype.card_sum]
  have horth : Orthonormal ℂ
      ((Set.univ : Set (Fin n ⊕ Fin n)).restrict (pairedVectors n v)) := by
    simpa only [Set.restrict, Function.comp_def] using
      (pairedVectors_orthonormal n v b hb).comp Subtype.val Subtype.val_injective
  obtain ⟨c, hc⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨c, fun i => hc i (Set.mem_univ i)⟩

def pairedMatrix (n : ℕ)
    (c : OrthonormalBasis (Fin n ⊕ Fin n) ℂ (V n)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (EuclideanSpace.basisFun (Fin n ⊕ Fin n) ℂ).toBasis.toMatrix c

theorem pairedMatrix_apply (n : ℕ)
    (c : OrthonormalBasis (Fin n ⊕ Fin n) ℂ (V n))
    (i j : Fin n ⊕ Fin n) :
    pairedMatrix n c i j = c j i := by
  simp [pairedMatrix, Module.Basis.toMatrix_apply,
    EuclideanSpace.basisFun_repr]

theorem pairedMatrix_unitary (n : ℕ)
    (c : OrthonormalBasis (Fin n ⊕ Fin n) ℂ (V n)) :
    pairedMatrix n c ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  exact (EuclideanSpace.basisFun (Fin n ⊕ Fin n) ℂ)
    |>.toMatrix_orthonormalBasis_mem_unitary c

theorem standardJ_pairedVectors_inl (n : ℕ) (v : Fin n → V n)
    (j : Fin n) :
    standardJ n (pairedVectors n v (Sum.inl j)) =
      -pairedVectors n v (Sum.inr j) := by
  simp [pairedVectors]

theorem standardJ_pairedVectors_inr (n : ℕ) (v : Fin n → V n)
    (j : Fin n) :
    standardJ n (pairedVectors n v (Sum.inr j)) =
      pairedVectors n v (Sum.inl j) := by
  simp only [pairedVectors, map_neg]
  have h := (standardQuaternionicStructure n).J_sq (v j)
  change standardJ n (standardJ n (v j)) = -(v j) at h
  rw [h]
  simp

theorem pairedMatrix_commutes_standardJ (n : ℕ) (v : Fin n → V n)
    (c : OrthonormalBasis (Fin n ⊕ Fin n) ℂ (V n))
    (hc : ∀ i, c i = pairedVectors n v i) :
    pairedMatrix n c * CompactSymplecticHaar.standardJ n =
      CompactSymplecticHaar.standardJ n * (pairedMatrix n c).map star := by
  ext i j
  cases i with
  | inl a =>
    cases j with
    | inl b =>
      simp [Matrix.mul_apply, CompactSymplecticHaar.standardJ,
        pairedMatrix_apply, hc, pairedVectors, standardJ_apply_inl,
        Matrix.one_apply]

    | inr b =>
      simp [Matrix.mul_apply, CompactSymplecticHaar.standardJ,
        pairedMatrix_apply, hc, pairedVectors, standardJ_apply_inl,
        standardJ_apply_inr, Matrix.one_apply]
  | inr a =>
    cases j with
    | inl b =>
      simp [Matrix.mul_apply, CompactSymplecticHaar.standardJ,
        pairedMatrix_apply, hc, pairedVectors,
        standardJ_apply_inr, Matrix.one_apply]
    | inr b =>
      simp [Matrix.mul_apply, CompactSymplecticHaar.standardJ,
        pairedMatrix_apply, hc, pairedVectors, standardJ_apply_inl,
        standardJ_apply_inr, Matrix.one_apply]

theorem pairedMatrix_mem_group (n : ℕ) (v : Fin n → V n)
    (c : OrthonormalBasis (Fin n ⊕ Fin n) ℂ (V n))
    (hc : ∀ i, c i = pairedVectors n v i) :
    (⟨pairedMatrix n c, pairedMatrix_unitary n c⟩ :
      Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ) ∈
      CompactSymplecticHaar.Group n := by
  exact (unitary_mem_stabilizer_iff_commutes_J n
    ⟨pairedMatrix n c, pairedMatrix_unitary n c⟩).mpr
      (pairedMatrix_commutes_standardJ n v c hc)

end
end QuaternionicSymmetry.OrbitalComplexEigenframe
