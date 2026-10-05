import QuaternionicSymmetry.QuaternionicTorusWeightKernel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! On the literal one-coordinate circle exponential, an integral
character has real derivative `t ↦ i μ_i t` at zero. This is an
elementary calculation independent of the chosen torus Lie atlas. -/

namespace QuaternionicSymmetry.TorusWeightCoordinateExponentialDerivative

open ManifoldQuaternionicTorusAction QuaternionicTorusWeightKernel
noncomputable section

def coordinateCircleExp {r : ℕ} (i : Fin r) (t : ℝ) : Torus r :=
  Pi.mulSingle i (Circle.exp t)

theorem coordinateCircleExp_zero {r : ℕ} (i : Fin r) :
    coordinateCircleExp i 0 = 1 := by
  classical
  simp [coordinateCircleExp]

theorem weightCharacter_coordinateCircleExp {r : ℕ}
    (μ : Fin r → ℤ) (i : Fin r) (t : ℝ) :
    (weightCharacter μ (coordinateCircleExp i t) : ℂ) =
      Complex.exp (Complex.I * (μ i : ℂ) * (t : ℂ)) := by
  rw [coordinateCircleExp, weightCharacter_mulSingle,
    ← Circle.exp_intCast_mul, Circle.coe_exp]
  congr 1
  push_cast
  ring

def coordinateCharacterDerivative {r : ℕ} (μ : Fin r → ℤ)
    (i : Fin r) : ℝ →L[ℝ] ℂ :=
  (Complex.I * (μ i : ℂ)) • Complex.ofRealCLM

theorem coordinateCharacterDerivative_apply {r : ℕ}
    (μ : Fin r → ℤ) (i : Fin r) (t : ℝ) :
    coordinateCharacterDerivative μ i t =
      Complex.I * (μ i : ℂ) * (t : ℂ) := by
  simp [coordinateCharacterDerivative]

theorem coordinateCharacterDerivative_ne_zero {r : ℕ}
    (μ : Fin r → ℤ) (i : Fin r) (hi : μ i ≠ 0) :
    coordinateCharacterDerivative μ i ≠ 0 := by
  intro hz
  have h := congrArg (fun f : ℝ →L[ℝ] ℂ => f 1) hz
  change coordinateCharacterDerivative μ i 1 = 0 at h
  rw [coordinateCharacterDerivative_apply] at h
  norm_num at h
  exact hi (by exact_mod_cast h)

theorem character_curve_hasFDerivAt_zero {r : ℕ}
    (μ : Fin r → ℤ) (i : Fin r) :
    HasFDerivAt
      (fun t : ℝ => (weightCharacter μ (coordinateCircleExp i t) : ℂ))
      (coordinateCharacterDerivative μ i) 0 := by
  have hArg : HasFDerivAt
      (fun t : ℝ => coordinateCharacterDerivative μ i t)
      (coordinateCharacterDerivative μ i) 0 :=
    (coordinateCharacterDerivative μ i).hasFDerivAt
  have hExp := hArg.cexp
  convert hExp using 1
  · funext t
    rw [weightCharacter_coordinateCircleExp,
      coordinateCharacterDerivative_apply]
  · simp [coordinateCharacterDerivative]

end
end QuaternionicSymmetry.TorusWeightCoordinateExponentialDerivative
