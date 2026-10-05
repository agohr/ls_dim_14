import QuaternionicSymmetry.QuaternionicStandardTracePowers

/-! Even trace powers of the extra quaternionic line in the standard action. -/
namespace QuaternionicSymmetry.QuaternionicScalarLineTracePowers
open QuaternionicProjectiveStandardLie QuaternionicScalarTrace
  ManifoldQuaternionicAdjointConnection LocalEndomorphismTrace
  QuaternionicLieAlgebraProjection
  QuaternionicStandardTracePowers
open scoped Quaternion
noncomputable section

private def rightMul (q : ℍ) : ℍ →L[ℝ] ℍ :=
  (ContinuousLinearMap.mul ℝ ℍ).flip q

private theorem rightMul_pow (q : ℍ) (j : ℕ) :
    (rightMul q) ^ j = rightMul (q ^ j) := by
  induction j with
  | zero =>
      apply ContinuousLinearMap.ext
      intro w
      simp [rightMul]
  | succ j ih =>
      rw [pow_succ, ih, pow_succ]
      apply ContinuousLinearMap.ext
      intro w
      change (w * q) * q ^ j = w * (q ^ j * q)
      rw [mul_assoc, ← pow_succ' q j, ← pow_succ q j]

private theorem trace_rightMul (q : ℍ) :
    traceCLM (rightMul q) = 4 * q.re := by
  rw [traceCLM_apply]
  change LinearMap.trace ℝ (ℍ[ℝ, -1, 0, -1])
    (rightMul q).toLinearMap = 4 * q.re
  rw [LinearMap.trace_eq_matrix_trace ℝ
      (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1))]
  simp [Matrix.trace, Fin.sum_univ_four, LinearMap.toMatrix_apply,
    QuaternionAlgebra.basisOneIJK]
  change (rightMul q ⟨1, 0, 0, 0⟩).re +
      (rightMul q ⟨0, 1, 0, 0⟩).imI +
      (rightMul q ⟨0, 0, 1, 0⟩).imJ +
      (rightMul q ⟨0, 0, 0, 1⟩).imK = 4 * q.re
  simp [rightMul, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  ring_nf

private theorem imaginary_sq (a : Fin 3 → ℝ) :
    (-(imaginary a)) ^ 2 =
      ((-(∑ i : Fin 3, a i * a i) : ℝ) : ℍ) := by
  have h := (Quaternion.sq_eq_neg_normSq).mpr (by simp : (-(imaginary a)).re = 0)
  rw [h]
  simp [Quaternion.normSq_def', Fin.sum_univ_three]
  simp only [pow_two]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  (S : QuaternionicStructure E) (A : E →L[ℝ] E)

theorem scalarLineLie_even_trace (j : ℕ) :
    traceCLM ((scalarLineLie S A) ^ (2 * j)) =
      4 * (-(∑ i : Fin 3,
        (axialProjection (adjointRepresentation S A)) i *
        (axialProjection (adjointRepresentation S A)) i)) ^ j := by
  let a := axialProjection (adjointRepresentation S A)
  let q := -(imaginary a)
  have hA : scalarLineLie S A = rightMul q := rfl
  rw [hA, rightMul_pow, trace_rightMul]
  have hq : q ^ (2 * j) =
      (((-(∑ i : Fin 3, a i * a i) : ℝ) ^ j : ℝ) : ℍ) := by
    rw [pow_mul, show q ^ 2 = ((-(∑ i : Fin 3, a i * a i) : ℝ) : ℍ) from
      imaginary_sq a]
    exact (map_pow (algebraMap ℝ ℍ) _ _).symm
  rw [hq]
  rfl

theorem standardLie_even_trace (j : ℕ) :
    traceCLM ((standardLie S A) ^ (2 * j)) =
      traceCLM ((symplecticProjection S A) ^ (2 * j)) +
      4 * (-(∑ i : Fin 3,
        (axialProjection (adjointRepresentation S A)) i *
        (axialProjection (adjointRepresentation S A)) i)) ^ j := by
  rw [standardLie_pow_trace, scalarLineLie_even_trace]

end
end QuaternionicSymmetry.QuaternionicScalarLineTracePowers
