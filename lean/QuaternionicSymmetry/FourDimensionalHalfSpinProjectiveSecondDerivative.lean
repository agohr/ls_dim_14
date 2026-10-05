import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondMobius
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondChart

/-! Exact derivatives and the connection gauge chain rule in the genuine
second CP¹ affine coordinate `[w:1]`, including `w = 0`.  These are algebraic
chart facts, not an identification with an external twistor convention. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondDerivative

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveSecondMobius

noncomputable section

theorem secondMobius_hasDerivAt (G : Mat2) (w : ℂ)
    (hden : secondDen G w ≠ 0) :
    HasDerivAt (secondMobius G)
      (Matrix.det (coordinateSwap * G * coordinateSwap) /
        (secondDen G w) ^ 2) w := by
  have hs : secondMobius G =
      mobius (coordinateSwap * G * coordinateSwap) := by
    funext z
    exact secondMobius_swap G z
  rw [hs, secondDen_swap] at *
  exact mobius_hasDerivAt _ w hden

theorem secondMobius_deriv (G : Mat2) (w : ℂ)
    (hden : secondDen G w ≠ 0) :
    deriv (secondMobius G) w =
      Matrix.det (coordinateSwap * G * coordinateSwap) /
        (secondDen G w) ^ 2 :=
  (secondMobius_hasDerivAt G w hden).deriv

def secondVaryingMobius (G C : Mat2) (w t : ℂ) : ℂ :=
  (secondNum G w + t * secondNum C w) /
    (secondDen G w + t * secondDen C w)

theorem secondVaryingMobius_swap (G C : Mat2) (w t : ℂ) :
    secondVaryingMobius G C w t =
      varyingMobius (coordinateSwap * G * coordinateSwap)
        (coordinateSwap * C * coordinateSwap) w t := by
  simp [secondVaryingMobius, varyingMobius,
    ← secondNum_swap, ← secondDen_swap]

theorem second_gauge_chain (G A B C : Mat2) (w : ℂ)
    (hG : G * B = A * G + C) (hden : secondDen G w ≠ 0) :
    deriv (secondMobius G) w * secondChartGenerator B w =
      secondChartGenerator A (secondMobius G w) +
        deriv (secondVaryingMobius G C w) 0 := by
  let S : Mat2 := coordinateSwap
  have hS : S * S = 1 := coordinateSwap_sq
  have hG' : (S * G * S) * (S * B * S) =
      (S * A * S) * (S * G * S) + (S * C * S) := by
    calc
      (S * G * S) * (S * B * S) = S * (G * B) * S := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc S S, hS,
          one_mul]
      _ = S * (A * G + C) * S := by rw [hG]
      _ = (S * A * S) * (S * G * S) + (S * C * S) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc S S, hS, one_mul]
  have hden' : chartDen (S * G * S) w ≠ 0 := by
    rwa [← secondDen_swap]
  have h := affine_gauge_chain (S * G * S) (S * A * S)
    (S * B * S) (S * C * S) w hG' hden'
  have hm : secondMobius G = mobius (S * G * S) := by
    funext z
    exact secondMobius_swap G z
  have hv : secondVaryingMobius G C w =
      varyingMobius (S * G * S) (S * C * S) w := by
    funext t
    exact secondVaryingMobius_swap G C w t
  simpa only [hm, hv, secondChartGenerator,
    S] using h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondDerivative
