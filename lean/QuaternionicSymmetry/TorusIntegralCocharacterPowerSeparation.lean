import QuaternionicSymmetry.ComplexProjectiveCocharacterLimit
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

/-! The positive nonunit real complex scalar `2` detects every integral
cocharacter exponent. This is the elementary scalar input for comparing
the fixed points of a generic one-parameter subgroup with those of its
full complex torus in actual projective coordinates. -/

namespace QuaternionicSymmetry.TorusIntegralCocharacterPowerSeparation

open ComplexProjectiveCocharacterLimit
noncomputable section

theorem twoUnit_zpow_injective :
    Function.Injective (fun a : ℤ => (twoUnit ^ a : ℂˣ)) := by
  intro a b h
  have hc := congrArg (fun z : ℂˣ => (z : ℂ)) h
  have hr : (2 : ℝ) ^ a = (2 : ℝ) ^ b := by
    have hc' : ((2 : ℝ) ^ a : ℂ) = ((2 : ℝ) ^ b : ℂ) := by
      simpa [twoUnit] using hc
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_zpow] using hc')
  exact (zpow_right_injective₀ (by norm_num : 0 < (2 : ℝ))
    (by norm_num : (2 : ℝ) ≠ 1)) hr

end
end QuaternionicSymmetry.TorusIntegralCocharacterPowerSeparation
