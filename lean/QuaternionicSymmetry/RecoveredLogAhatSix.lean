import QuaternionicSymmetry.RecoveredLogAhat
import QuaternionicSymmetry.DimensionThirteenFourteenDensity

/-! The sixth logarithmic A-hat coefficient after recovering standard
quaternionic power sums from tangent half traces. -/
namespace QuaternionicSymmetry.RecoveredLogAhatSix
open MvPolynomial QuaternionicTangentRootConversion
noncomputable section
set_option maxHeartbeats 2000000

abbrev P := DimensionThirteenFourteenDensity.P

def tangentVariables : ℕ → P := fun j =>
  if h : j < 7 then X ⟨j, h⟩ else 0

def recoveredValues (n : ℕ) : Fin 7 → P :=
  ![X 0,
    recoveredStandardPower n (X 0) tangentVariables 1,
    recoveredStandardPower n (X 0) tangentVariables 2,
    recoveredStandardPower n (X 0) tangentVariables 3,
    recoveredStandardPower n (X 0) tangentVariables 4,
    recoveredStandardPower n (X 0) tangentVariables 5,
    recoveredStandardPower n (X 0) tangentVariables 6]

theorem recovered_logarithmic_six (n : ℕ) :
    aeval (recoveredValues n) (DimensionThirteenFourteenDensity.b6 n) =
      C (LogAhat.ell 6) * tangentVariables 6 := by
  apply MvPolynomial.funext
  intro v
  change (aeval v) ((aeval (recoveredValues n))
    (DimensionThirteenFourteenDensity.b6 n)) =
      (aeval v) (C (LogAhat.ell 6) * tangentVariables 6)
  rw [comp_aeval_apply]
  simp [DimensionThirteenFourteenDensity.b6, recoveredValues,
    DimensionThirteenFourteenDensity.u,
    DimensionThirteenFourteenDensity.p1,
    DimensionThirteenFourteenDensity.p2,
    DimensionThirteenFourteenDensity.p3,
    DimensionThirteenFourteenDensity.p4,
    DimensionThirteenFourteenDensity.p5,
    DimensionThirteenFourteenDensity.p6,
    recoveredStandardPower, recoveredSymplecticPowers,
    recoveredQ1, recoveredQ2, recoveredQ3, recoveredQ4, recoveredQ5,
    recoveredQ6, half, tangentVariables, LogAhat.ell_six]
  ring

variable {R : Type} [CommRing R] [Algebra ℚ R]

def tangentValues (u : R) (t : ℕ → R) : Fin 7 → R :=
  ![u, t 1, t 2, t 3, t 4, t 5, t 6]

def standardValues (n : ℕ) (u : R) (t : ℕ → R) : Fin 7 → R :=
  ![u, recoveredStandardPower n u t 1, recoveredStandardPower n u t 2,
    recoveredStandardPower n u t 3, recoveredStandardPower n u t 4,
    recoveredStandardPower n u t 5, recoveredStandardPower n u t 6]

theorem evaluate_recoveredValues (n : ℕ) (u : R) (t : ℕ → R) :
    (fun i => (aeval (tangentValues u t)) (recoveredValues n i)) =
      standardValues n u t := by
  funext i
  fin_cases i <;>
    simp [recoveredValues, standardValues, tangentValues,
      recoveredStandardPower, recoveredSymplecticPowers,
      recoveredQ1, recoveredQ2, recoveredQ3, recoveredQ4, recoveredQ5,
      recoveredQ6, half, tangentVariables]

theorem evaluated_logarithmic_six (n : ℕ) (u : R) (t : ℕ → R) :
    aeval (standardValues n u t) (DimensionThirteenFourteenDensity.b6 n) =
      algebraMap ℚ R (LogAhat.ell 6) * t 6 := by
  have h := congrArg (aeval (tangentValues u t)) (recovered_logarithmic_six n)
  rw [comp_aeval_apply, evaluate_recoveredValues] at h
  rw [h, map_mul, aeval_C]
  simp [tangentVariables, tangentValues]

end
end QuaternionicSymmetry.RecoveredLogAhatSix
