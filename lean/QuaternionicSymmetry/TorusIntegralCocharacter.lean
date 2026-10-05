import QuaternionicSymmetry.TorusLaurentRepresentation

/-! Actual one-parameter subgroups of the complex torus attached to integer
vectors, and the literal character/cocharacter pairing. These are algebraic
identities used in projective orbit limits, not a fixed-weight span premise. -/
namespace QuaternionicSymmetry.TorusIntegralCocharacter

open TorusLaurentRepresentation
open scoped BigOperators
noncomputable section

variable {r : ℕ}

def cocharacter (u : Fin r → ℤ) : ℂˣ →* ComplexTorus r where
  toFun z i := z ^ u i
  map_one' := by ext i; simp
  map_mul' z w := by ext i; simp [mul_zpow]

def pairing (μ u : Fin r → ℤ) : ℤ := ∑ i : Fin r, μ i * u i

theorem character_cocharacter (μ u : Fin r → ℤ) (z : ℂˣ) :
    complexWeightCharacter μ (cocharacter u z) = z ^ pairing μ u := by
  change (∏ i : Fin r, (z ^ u i) ^ μ i) = z ^ ∑ i : Fin r, μ i * u i
  simp_rw [← zpow_mul, mul_comm (u _)]
  have h (s : Finset (Fin r)) :
      (∏ i ∈ s, z ^ (μ i * u i)) = z ^ ∑ i ∈ s, μ i * u i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih, zpow_add]
  exact h Finset.univ

/-- Normalize an integral-character coordinate by a maximal exponent.
All remaining powers are ordinary nonnegative powers of the inverse. -/
theorem normalized_character (μ u : Fin r → ℤ) (m : ℤ)
    (hm : pairing μ u ≤ m) (z : ℂˣ) :
    (z ^ (-m) : ℂˣ) * (complexWeightCharacter μ (cocharacter u z) : ℂ) =
      ((z⁻¹ : ℂˣ) : ℂ) ^ (m - pairing μ u).toNat := by
  rw [character_cocharacter]
  have hcast : ((m - pairing μ u).toNat : ℤ) = m - pairing μ u :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hm)
  have heq : z ^ (-m) * z ^ pairing μ u =
      (z⁻¹) ^ (m - pairing μ u).toNat := by
    rw [← zpow_add, ← zpow_natCast, hcast, inv_zpow, ← zpow_neg]
    congr 1
    omega
  exact congrArg (fun w : ℂˣ => (w : ℂ)) heq

end
end QuaternionicSymmetry.TorusIntegralCocharacter
