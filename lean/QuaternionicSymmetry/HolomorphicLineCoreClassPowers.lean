import QuaternionicSymmetry.HolomorphicLineCoreClassGroup
import QuaternionicSymmetry.HolomorphicLineTensorPowerClasses

/-! Natural and integral powers in the group of represented holomorphic
line-core classes are the actual scalar-cocycle powers. In particular,
negative group powers represent dual line bundles, not formal symbols.
No assertion that these classes exhaust analytic invertible sheaves is made. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreClassPowers

open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicLineTensorPowerClasses HolomorphicLineTensorGroupGauges
open HolomorphicLineIntegerPowers
open scoped Manifold ContDiff
noncomputable section

universe u
variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

theorem tensorIterate_eq_pow (L : LineCore.{u} (B := B) IB) (k : ℕ) :
    tensorIterate IB L k = (Quotient.mk _ L : CoreClass IB) ^ k := by
  induction k with
  | zero =>
      rw [pow_zero]
      change Quotient.mk _ (powerCoreRep IB L 0) = Quotient.mk _ (trivialLine IB)
      apply Quotient.sound
      letI := L.holomorphic
      exact ⟨zeroPowerTrivialGauge L.core⟩
  | succ k ih =>
      rw [tensorIterate, ih, pow_succ]
      rfl

theorem class_powerCoreRep (L : LineCore.{u} (B := B) IB) (k : ℕ) :
    (Quotient.mk _ (powerCoreRep IB L k) : CoreClass IB) =
      (Quotient.mk _ L : CoreClass IB) ^ k :=
  (tensorIterate_eq_power IB L k).symm.trans (tensorIterate_eq_pow IB L k)

/-- The genuine integral scalar-cocycle power as a represented line. -/
def integerPowerCoreRep (L : LineCore.{u} (B := B) IB) (r : ℤ) :
    LineCore.{u} (B := B) IB := by
  letI := L.holomorphic
  exact {
    Index := L.Index
    core := integerPowerCore L.core r
    holomorphic := inferInstance }

theorem integerPowerCoreRep_natCast (L : LineCore.{u} (B := B) IB) (k : ℕ) :
    integerPowerCoreRep IB L (k : ℤ) = powerCoreRep IB L k := by
  simp only [integerPowerCoreRep, integerPowerCore_natCast, powerCoreRep]

theorem integerPowerCoreRep_neg_natCast (L : LineCore.{u} (B := B) IB)
    (k : ℕ) (hk : 0 < k) :
    integerPowerCoreRep IB L (-(k : ℤ)) = powerCoreRep IB (L.dual IB) k := by
  simp only [integerPowerCoreRep, integerPowerCore_neg_natCast L.core k hk,
    powerCoreRep, LineCore.dual]

theorem class_integerPowerCoreRep (L : LineCore.{u} (B := B) IB) (r : ℤ) :
    (Quotient.mk _ (integerPowerCoreRep IB L r) : CoreClass IB) =
      (Quotient.mk _ L : CoreClass IB) ^ r := by
  cases r with
  | ofNat k =>
      change (Quotient.mk _ (integerPowerCoreRep IB L (k : ℤ)) : CoreClass IB) =
        (Quotient.mk _ L : CoreClass IB) ^ (k : ℤ)
      rw [integerPowerCoreRep_natCast, class_powerCoreRep, zpow_natCast]
  | negSucc k =>
      change (Quotient.mk _ (integerPowerCoreRep IB L (-((k + 1 : ℕ) : ℤ))) :
        CoreClass IB) = _
      rw [integerPowerCoreRep_neg_natCast IB L (k + 1) (Nat.succ_pos k),
        class_powerCoreRep]
      change ((Quotient.mk _ L : CoreClass IB)⁻¹) ^ (k + 1) = _
      simp only [inv_pow, zpow_negSucc]

end
end QuaternionicSymmetry.HolomorphicLineCoreClassPowers
