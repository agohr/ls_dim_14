import QuaternionicSymmetry.QuaternionicWeylMatrixCoefficients
import QuaternionicSymmetry.QuaternionicSourceMatrixTrace
import QuaternionicSymmetry.QuaternionicUpperBlockTraceForms
import Mathlib.Algebra.MvPolynomial.Funext

/-! The zero quaternionic line can be removed from every positive source
trace polynomial, including substitution into an exterior coefficient algebra. -/
namespace QuaternionicSymmetry.QuaternionicWeylRankReduction
open QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureMatrixExpansion
open QuaternionicWeylMatrixCoefficients QuaternionicSourceMatrixTrace
open QuaternionicUpperBlockTraceForms QuaternionicProjectiveStandardHilbertStructure
open MatrixTracePolynomial CompactSymplecticTraceInvariants
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (QuaternionicProjectiveStandardL2.StandardSpace (E := E)) :=
  inferInstance

theorem upperCLM_pow_succ (A : E →L[ℝ] E) (k : ℕ) :
    upperCLM (A ^ (k + 1)) = upperCLM A ^ (k + 1) := by
  induction k with
  | zero => simp only [Nat.zero_add, pow_one]
  | succ k ih =>
      rw [pow_succ, upperCLM_mul, ih]
      simp only [pow_succ]

theorem source_evenTrace_eq (A : operatorSpace S) (j : ℕ) (hj : 0 < j) :
    evenTracePower (sourceMatrixMap S A).val j =
      evenTracePower (tangentSourceMatrixMap S A).val j := by
  have hs := source_normalized_trace (standardStructure S) (upperCentralizerMap S A)
    (1 / (2 * Real.pi)) j hj
  have ht := source_normalized_trace S (centralizerMap S A) (1 / (2 * Real.pi)) j hj
  have he : 2 * j = (2 * j - 1) + 1 := by omega
  have hp := upperCLM_pow_succ A.val (2 * j - 1)
  rw [← he] at hp
  change ((-1 : ℝ) ^ j / 2) * ((sourceMatrixMap S A).val ^ (2 * j)).trace.re =
    _ * LocalEndomorphismTrace.traceCLM (upperCLM A.val ^ (2 * j)) at hs
  rw [← hp, upperCLM_trace] at hs
  change ((-1 : ℝ) ^ j / 2) * ((tangentSourceMatrixMap S A).val ^ (2 * j)).trace.re =
    _ * LocalEndomorphismTrace.traceCLM (A.val ^ (2 * j)) at ht
  have h := mul_left_cancel₀ (show (-1 : ℝ) ^ j / 2 ≠ 0 by positivity) (hs.trans ht.symm)
  unfold evenTracePower
  rw [h]

theorem source_combination (x : Index S → ℝ) :
    matrixCombination (fun a => (sourceMatrixMap S (operatorBasis S a)).val) x =
      (sourceMatrixMap S (∑ a, x a • operatorBasis S a)).val := by
  simp only [matrixCombination, map_sum, map_smul, Submodule.coe_sum,
    Submodule.coe_smul, Complex.coe_smul]

theorem tangent_combination (x : Index S → ℝ) :
    matrixCombination (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).val) x =
      (tangentSourceMatrixMap S (∑ a, x a • operatorBasis S a)).val := by
  simp only [matrixCombination, map_sum, map_smul, Submodule.coe_sum,
    Submodule.coe_smul, Complex.coe_smul]

theorem tracePolynomial_eq (j : ℕ) (hj : 0 < j) :
    tracePowerPolynomial (fun a => (sourceMatrixMap S (operatorBasis S a)).val) j =
      tracePowerPolynomial (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).val) j := by
  apply MvPolynomial.funext
  intro x
  rw [eval_tracePowerPolynomial, eval_tracePowerPolynomial,
    source_combination, tangent_combination]
  exact source_evenTrace_eq S _ j hj

theorem signedTrace_eq {R : Type*} [CommRing R] [Algebra ℝ R]
    (η : Index S → R) (j : ℕ) (hj : 0 < j) :
    signedTracePower (complexifiedMatrix
      (fun a => (sourceMatrixMap S (operatorBasis S a)).val) η) j =
    signedTracePower (complexifiedMatrix
      (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).val) η) j := by
  have h := congrArg (MvPolynomial.aeval η) (tracePolynomial_eq S j hj)
  rw [aeval_tracePowerPolynomial, aeval_tracePowerPolynomial] at h
  exact congrArg (fun z => (-1 : R) ^ j * z) h

theorem traceRepresentative_eq {ι : Type*} [Fintype ι]
    (W : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (hW : ∀ u v, (W u v).toLinearMap ∈ S.skewCentralizer)
    (b : Module.Basis ι ℝ E) (j : ℕ) (hj : 0 < j) :
    QuaternionicWeylExteriorTrace.traceRepresentative S W hW b j =
      tangentTraceRepresentative S W hW b j := by
  apply Subtype.ext
  rw [QuaternionicWeylExteriorTrace.traceRepresentative_val S W hW b j hj,
    tangentTraceRepresentative_val S W hW b j hj]
  exact congrArg Subtype.val (signedTrace_eq S
    (QuaternionicCurvatureOrbitalSign.coefficientExterior S W hW b) j hj)

end
end QuaternionicSymmetry.QuaternionicWeylRankReduction
