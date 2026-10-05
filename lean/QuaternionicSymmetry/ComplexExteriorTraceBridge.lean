import QuaternionicSymmetry.ExteriorMatrixLinearCombination
import QuaternionicSymmetry.ContinuousAlgebraWedgePowers

/-! The signed trace in the complexified even exterior algebra is paired
with the actual signed complex matrix wedge trace, via realification. -/
namespace QuaternionicSymmetry.ComplexExteriorTraceBridge
open ExteriorContinuousPairing ExteriorMatrixWedgeBridge ExteriorMatrixTraceBridge
open ExteriorMatrixLinearCombination ComplexMatrixRealificationAlgebra
open ComplexMatrixRealification QuaternionicExteriorEvenTrace EvenForms
open ContinuousAlgebraWedgePowers MatrixTracePolynomial
noncomputable section
variable {V β κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype β] [Fintype κ] [DecidableEq κ]
local instance : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
local instance : NormedRing (Matrix (κ × Fin 2) (κ × Fin 2) ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix (κ × Fin 2) (κ × Fin 2) ℝ) :=
  Matrix.linftyOpNormedAlgebra
variable (B : β → Matrix κ κ ℂ) (η : β → Power V 2)

def combinationForm : V [⋀^Fin 2]→L[ℝ] Matrix κ κ ℂ :=
  ∑ b, (toContinuous 2 (η b)).smulRight (B b)

theorem realify_combinationForm :
    realifyCLM.compContinuousAlternatingMap (combinationForm B η) =
      matrixTwoForm (exteriorMatrix (fun b => realify (B b)) η)
        (entries_two (fun b => realify (B b)) η) := by
  apply ContinuousAlternatingMap.ext
  intro v
  rw [ExteriorMatrixLinearCombination.matrixTwoForm_apply]
  change realifyCLM (combinationForm B η v) = _
  simp only [combinationForm, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smulRight_apply, map_sum, map_smul]
  rfl

def signedExteriorTrace (j : ℕ) : Power V (wedgeDegree (2 * j - 1)) :=
  ((-1 : ℝ) ^ j / 4) •
    wedgeTrace (exteriorMatrix (fun b => realify (B b)) η)
      (entries_two (fun b => realify (B b)) η) (2 * j - 1)

omit [FiniteDimensional ℝ V] in
theorem signedExteriorTrace_val (j : ℕ) (hj : 0 < j) :
    (signedExteriorTrace B η j).val =
      (signedTracePower (complexifiedMatrix B (fun b => ofTwoForm (η b))) j : EvenAlgebra V).val := by
  rw [RealifiedTracePolynomial.signedTracePower_eq_realified]
  have he : 2 * j - 1 + 1 = 2 * j := by omega
  simp only [signedExteriorTrace, Submodule.coe_smul, wedgeTrace, he,
    exteriorMatrix]
  rfl

theorem paired_signedTrace (j : ℕ) (v : Fin (wedgeDegree (2 * j - 1)) → V) :
    toContinuous (wedgeDegree (2 * j - 1)) (signedExteriorTrace B η j) v =
      ((-1 : ℝ) ^ j / 2) * (power (combinationForm B η) (2 * j - 1) v).trace.re := by
  let A := exteriorMatrix (fun b => realify (B b)) η
  let hA := entries_two (fun b => realify (B b)) η
  have hm := map_power realifyCLM realifyCLM_mul (combinationForm B η) (2 * j - 1)
  rw [realify_combinationForm B η] at hm
  have hv := congrArg (fun α => α v) hm
  have hp (γ : V [⋀^Fin 2]→L[ℝ] Matrix (κ × Fin 2) (κ × Fin 2) ℝ) (k : ℕ) :
      power γ k = matrixWedgePower γ k := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [power, matrixWedgePower, ih]
  change realify (power (combinationForm B η) (2 * j - 1) v) =
    power (matrixTwoForm A hA) (2 * j - 1) v at hv
  rw [hp] at hv
  have ht := congrArg (fun α => α v) (trace_matrixWedgePower A hA (2 * j - 1))
  change Matrix.trace (matrixWedgePower (matrixTwoForm A hA) (2 * j - 1) v) =
    toContinuous (wedgeDegree (2 * j - 1)) (wedgeTrace A hA (2 * j - 1)) v at ht
  rw [← hv, trace_realify] at ht
  change toContinuous (wedgeDegree (2 * j - 1))
    (((-1 : ℝ) ^ j / 4) • wedgeTrace A hA (2 * j - 1)) v = _
  rw [toContinuous_smul, ContinuousAlternatingMap.smul_apply, ← ht]
  simp only [smul_eq_mul]
  ring

end
end QuaternionicSymmetry.ComplexExteriorTraceBridge
