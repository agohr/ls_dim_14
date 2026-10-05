import QuaternionicSymmetry.Characters
import Mathlib.RingTheory.PowerSeries.Exp

/-! The formal exponential substitution underlying the character coefficient table.

The map here is an algebra homomorphism from Laurent polynomials into actual
formal power series. Thus both the character identities and their coefficients
can be used together without assuming a formal substitution rule.
-/

namespace QuaternionicSymmetry.CharacterSeries

open LaurentPolynomial

noncomputable section

def exponentialMonoid : Multiplicative ℤ →* PowerSeries ℚ where
  toFun m := PowerSeries.rescale (m.toAdd : ℚ) (PowerSeries.exp ℚ)
  map_one' := by simp
  map_mul' m n := by
    change PowerSeries.rescale ((m.toAdd + n.toAdd : ℤ) : ℚ) (PowerSeries.exp ℚ) = _
    rw [Int.cast_add, PowerSeries.exp_mul_exp_eq_exp_add]

/-- Formally substitute `T^m = exp(mh)`, preserving sums and products. -/
def characterSeries : LaurentPolynomial ℚ →ₐ[ℚ] PowerSeries ℚ :=
  AddMonoidAlgebra.lift ℚ (PowerSeries ℚ) ℤ exponentialMonoid

@[simp] theorem characterSeries_T (m : ℤ) :
    characterSeries (T m) = PowerSeries.rescale (m : ℚ) (PowerSeries.exp ℚ) := by
  change AddMonoidAlgebra.lift ℚ (PowerSeries ℚ) ℤ exponentialMonoid
    (Finsupp.single m 1) = _
  rw [AddMonoidAlgebra.lift_single]
  exact one_smul ℚ _

/-- The earlier finite coefficient calculation is the actual formal-series coefficient. -/
theorem coefficient_characterSeries (j : ℕ) (p : LaurentPolynomial ℚ) :
    PowerSeries.coeff (2 * j) (characterSeries p) = Characters.taylorCoefficient j p := by
  have h : (PowerSeries.coeff (2 * j)).comp characterSeries.toLinearMap =
      Characters.taylorCoefficient j := by
    apply Finsupp.lhom_ext
    intro m a
    change PowerSeries.coeff (2 * j)
      (AddMonoidAlgebra.lift ℚ (PowerSeries ℚ) ℤ exponentialMonoid (Finsupp.single m a)) =
      Finsupp.linearCombination ℚ
        (fun m : ℤ => (m : ℚ) ^ (2 * j) / (Nat.factorial (2 * j) : ℚ))
        (Finsupp.single m a)
    rw [AddMonoidAlgebra.lift_single, Finsupp.linearCombination_single]
    change PowerSeries.coeff (2 * j)
      (a • PowerSeries.rescale (m : ℚ) (PowerSeries.exp ℚ)) = _
    rw [map_smul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    simp [div_eq_mul_inv]
  exact LinearMap.congr_fun h p

/-- The virtual character becomes precisely the indicated hyperbolic expression. -/
theorem virtual_series (n : ℕ) :
    characterSeries (Characters.virtual n) =
      if n % 2 = 0 then
        (PowerSeries.rescale 1 (PowerSeries.exp ℚ) -
          PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) ^ (n + 2)
      else
        (PowerSeries.rescale 1 (PowerSeries.exp ℚ) -
          PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) ^ (n + 1) *
        (PowerSeries.rescale 1 (PowerSeries.exp ℚ) +
          PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) := by
  unfold Characters.virtual
  split_ifs <;> simp

end
end QuaternionicSymmetry.CharacterSeries
