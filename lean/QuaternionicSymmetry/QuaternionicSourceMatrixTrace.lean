import QuaternionicSymmetry.QuaternionicComplexMatrixAlgebra
import QuaternionicSymmetry.ComplexEvenTraceNormalization

/-! Positive even traces of the fixed source matrix have quarter-real
trace normalization for every skew quaternionic operator. -/
namespace QuaternionicSymmetry.QuaternionicSourceMatrixTrace
open QuaternionicComplexMatrixAlgebra QuaternionicOperatorMatrixLinear
open ComplexEvenTraceNormalization LocalEndomorphismTrace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)
local instance : NormedSpace ℝ E := inferInstance

def skewToComplexAlgebra (A : S.skewCentralizer) : complexLinearAlgebra S :=
  ⟨A.val.toContinuousLinearMap, (mem_complexLinearAlgebra S _).mpr
    ((S.mem_skewCentralizer_iff A.val).mp A.property).2.1⟩

theorem source_normalized_trace (A : S.skewCentralizer) (r : ℝ) (j : ℕ) (hj : 0 < j) :
    ((-1 : ℝ) ^ j / 2) * ((r • (hermitianMatrixMap S A).val) ^ (2 * j)).trace.re =
      (r ^ (2 * j) / 4) * traceCLM ((A.val.toContinuousLinearMap) ^ (2 * j)) := by
  let C := skewToComplexAlgebra S A
  have he : 2 * j = (2 * j - 1) + 1 := by omega
  have hp := matrixLinear_pow_succ S C (2 * j - 1)
  rw [← he] at hp
  have htr := matrixLinear_trace S (C ^ (2 * j))
  rw [hp] at htr
  change ((-1 : ℝ) ^ j / 2) *
    ((r • (Complex.I • matrixLinear S C)) ^ (2 * j)).trace.re = _
  rw [← Complex.coe_smul r, ← mul_smul, smul_pow, Matrix.trace_smul]
  change ((-1 : ℝ) ^ j / 2) *
    (((r : ℂ) * Complex.I) ^ (2 * j) * (matrixLinear S C ^ (2 * j)).trace).re = _
  rw [imaginary_scale_even]
  change (r ^ (2 * j) / 2) * (matrixLinear S C ^ (2 * j)).trace.re =
    (r ^ (2 * j) / 4) * traceCLM (C ^ (2 * j)).val
  rw [htr]
  ring

end
end QuaternionicSymmetry.QuaternionicSourceMatrixTrace
