import QuaternionicSymmetry.QuaternionicScalarLineTracePowers
import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionLaws

/-! The rank-three adjoint operator has eigenvalue zero and its two
nonzero eigenvalues square to minus four times the scalar norm. -/
namespace QuaternionicSymmetry.QuaternionicRankThreeTracePowers
open ManifoldQuaternionicAdjointConnection
  QuaternionicLieAlgebraProjection
  QuaternionicStandardTracePowers
  VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicRankThreeOrientation
  LocalEndomorphismTrace QuaternionicScalarTrace
noncomputable section

private def t (a : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, a i * a i

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  (S : QuaternionicStructure E) (a : Fin 3 → ℝ)

private theorem adjoint_cubic :
    (adjointRepresentation S (synth S a)) ^ 3 =
      (-(4 * t a) : ℝ) • adjointRepresentation S (synth S a) := by
  apply ContinuousLinearMap.ext
  intro b
  ext i
  fin_cases i <;>
    simp [pow_succ, ContinuousLinearMap.mul_apply,
      adjointRepresentation_synth, crossProduct, t, Fin.sum_univ_three] <;>
    ring

theorem adjoint_even_trace (j : ℕ) (hj : 0 < j) :
    traceCLM ((adjointRepresentation S (synth S a)) ^ (2 * j)) =
      2 * (-(4 * t a)) ^ j := by
  let C := adjointRepresentation S (synth S a)
  have hcubic : C ^ 3 = (-(4 * t a) : ℝ) • C := adjoint_cubic S a
  have hbase : traceCLM (C ^ 2) = 2 * (-(4 * t a)) := by
    rw [pow_two, trace_adjoint_synth_product]
    simp [t]
    ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  induction m with
  | zero => simpa using hbase
  | succ m ih =>
      have hpow : C ^ (2 * (m + 1 + 1)) =
          (-(4 * t a) : ℝ) • C ^ (2 * (m + 1)) := by
        calc
          C ^ (2 * (m + 1 + 1)) = C ^ (2 * m + 1) * C ^ 3 := by
            rw [← pow_add]
            congr 1
          _ = C ^ (2 * m + 1) * ((-(4 * t a) : ℝ) • C) := by rw [hcubic]
          _ = (-(4 * t a) : ℝ) • C ^ (2 * (m + 1)) := by
            rw [mul_smul_comm, ← pow_succ]
            congr 1
      rw [hpow, map_smul, ih (by omega)]
      simp only [smul_eq_mul]
      conv_rhs => rw [pow_succ]
      conv_lhs => rw [pow_succ]
      ring_nf

/-- The quaternionic line and the three-dimensional adjoint block have a
different ratio in each positive even degree. For `j = 1` this reduces to
the one-half factor of the first Pontryagin normalization. -/
theorem scalarLine_even_trace_rankThree (A : E →L[ℝ] E)
    (j : ℕ) (hj : 0 < j) :
    (4 : ℝ) ^ j *
      traceCLM ((QuaternionicProjectiveStandardLie.scalarLineLie S A) ^ (2 * j)) =
      2 * traceCLM
        ((adjointRepresentation S
          (QuaternionicLieAlgebraProjection.scalarProjection S A)) ^ (2 * j)) := by
  let a := QuaternionicLieAlgebraProjection.axialProjection
    (adjointRepresentation S A)
  change (4 : ℝ) ^ j *
      traceCLM ((QuaternionicProjectiveStandardLie.scalarLineLie S A) ^ (2 * j)) =
    2 * traceCLM ((adjointRepresentation S (synth S a)) ^ (2 * j))
  rw [QuaternionicScalarLineTracePowers.scalarLineLie_even_trace,
    adjoint_even_trace S a j hj]
  change (4 : ℝ) ^ j * (4 * (-t a) ^ j) =
    2 * (2 * (-(4 * t a)) ^ j)
  rw [show -(4 * t a) = 4 * (-t a) by ring, mul_pow]
  ring

theorem standard_even_trace_rankThree (A : E →L[ℝ] E)
    (j : ℕ) (hj : 0 < j) :
    (4 : ℝ) ^ j *
      traceCLM ((QuaternionicProjectiveStandardLie.standardLie S A) ^ (2 * j)) =
      (4 : ℝ) ^ j *
        traceCLM ((symplecticProjection S A) ^ (2 * j)) +
      2 * traceCLM
        ((adjointRepresentation S (scalarProjection S A)) ^ (2 * j)) := by
  rw [standardLie_pow_trace]
  rw [mul_add, scalarLine_even_trace_rankThree S A j hj]

end
end QuaternionicSymmetry.QuaternionicRankThreeTracePowers
