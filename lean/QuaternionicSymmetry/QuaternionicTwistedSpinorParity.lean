import Mathlib.Tactic

/-! The algebraic central-sign calculation for the local twisted-spinor
representation. This establishes precisely which symmetric powers can
descend through the simultaneous central sign; constructing the smooth
global bundle and its Dirac operator remains separate. -/
namespace QuaternionicSymmetry.QuaternionicTwistedSpinorParity

theorem central_sign_trivial_iff (n q : ℕ) :
    (-1 : ℚ)^n * (-1 : ℚ)^q = 1 ↔ q % 2 = n % 2 := by
  rw [← pow_add, neg_one_pow_eq_one_iff_even (by norm_num)]
  rw [Nat.even_iff]
  omega

theorem central_sign_trivial_of_twist (n : ℕ) (r : ℤ)
    (hqr : 0 ≤ (n : ℤ) + 2*r) :
    (-1 : ℚ)^n * (-1 : ℚ)^(((n : ℤ) + 2*r).toNat) = 1 := by
  apply (central_sign_trivial_iff n _).2
  omega

end QuaternionicSymmetry.QuaternionicTwistedSpinorParity
