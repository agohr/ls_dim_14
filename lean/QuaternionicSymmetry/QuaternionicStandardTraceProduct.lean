import QuaternionicSymmetry.QuaternionicProjectiveStandardLie
import QuaternionicSymmetry.QuaternionicScalarTrace

/-! Real trace of the standard block action: the quaternionic line contributes
one half of the trace in the induced three-dimensional adjoint action. -/
namespace QuaternionicSymmetry.QuaternionicStandardTraceProduct

open QuaternionicProjectiveStandardLie
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicProjectiveStandardL2
  QuaternionicScalarTrace LocalEndomorphismTrace
  QuaternionicLieAlgebraProjection
  ManifoldQuaternionicAdjointConnection
  VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Quaternion
noncomputable section

private def rightMul (q : ℍ) : ℍ →L[ℝ] ℍ :=
  (ContinuousLinearMap.mul ℝ ℍ).flip q

private theorem rightMul_apply (q w : ℍ) : rightMul q w = w * q := rfl

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
  simp [rightMul_apply, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

private theorem rightMul_mul (q r : ℍ) :
    rightMul q * rightMul r = rightMul (r * q) := by
  apply ContinuousLinearMap.ext
  intro w
  change (w * r) * q = w * (r * q)
  exact mul_assoc w r q

private theorem trace_rightImag_product (a b : Fin 3 → ℝ) :
    traceCLM (rightMul (-(imaginary a)) * rightMul (-(imaginary b))) =
      -4 * ∑ i : Fin 3, a i * b i := by
  rw [rightMul_mul, trace_rightMul]
  simp [Quaternion.re_mul, imaginary_re, imaginary_imI,
    imaginary_imJ, imaginary_imK, Fin.sum_univ_three]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  (S : QuaternionicStructure E)

theorem scalarLineLie_product_trace (A B : E →L[ℝ] E) :
    traceCLM (scalarLineLie S A * scalarLineLie S B) =
      (1 / 2 : ℝ) *
        traceCLM
          (adjointRepresentation S (scalarProjection S A) *
            adjointRepresentation S (scalarProjection S B)) := by
  let a := axialProjection
    (ManifoldQuaternionicAdjointConnection.adjointRepresentation S A)
  let b := axialProjection
    (ManifoldQuaternionicAdjointConnection.adjointRepresentation S B)
  have hA : scalarLineLie S A = rightMul (-(imaginary a)) := rfl
  have hB : scalarLineLie S B = rightMul (-(imaginary b)) := rfl
  rw [hA, hB, trace_rightImag_product]
  change -4 * ∑ i : Fin 3, a i * b i =
    (1 / 2 : ℝ) *
      traceCLM (adjointRepresentation S (synth S a) *
        adjointRepresentation S (synth S b))
  rw [trace_adjoint_synth_product]
  ring

theorem standardLie_product_trace (A B : E →L[ℝ] E) :
    traceCLM (standardLie S A * standardLie S B) =
      traceCLM (symplecticProjection S A * symplecticProjection S B) +
        (1 / 2 : ℝ) *
          traceCLM
            (adjointRepresentation S (scalarProjection S A) *
              adjointRepresentation S (scalarProjection S B)) := by
  let c := WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ
  have hblock :
      c.toLinearEquiv.conj
        (standardLie S A * standardLie S B).toLinearMap =
      LinearMap.prodMap
        (symplecticProjection S A * symplecticProjection S B).toLinearMap
        (scalarLineLie S A * scalarLineLie S B).toLinearMap := by
    apply LinearMap.ext
    intro z
    apply Prod.ext
    · change (c (standardLie S A (standardLie S B (c.symm z)))).1 = _
      rw [standardLie_blocks, standardLie_blocks]
      simp [c]
    · change (c (standardLie S A (standardLie S B (c.symm z)))).2 = _
      rw [standardLie_blocks, standardLie_blocks]
      simp [c]
  have htrace := LinearMap.trace_conj'
    (standardLie S A * standardLie S B).toLinearMap c.toLinearEquiv
  rw [hblock, LinearMap.trace_prodMap'] at htrace
  change traceCLM (symplecticProjection S A * symplecticProjection S B) +
      traceCLM (scalarLineLie S A * scalarLineLie S B) =
      traceCLM (standardLie S A * standardLie S B) at htrace
  rw [scalarLineLie_product_trace S A B] at htrace
  exact htrace.symm

end
end QuaternionicSymmetry.QuaternionicStandardTraceProduct
