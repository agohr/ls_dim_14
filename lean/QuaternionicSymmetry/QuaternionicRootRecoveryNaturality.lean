import QuaternionicSymmetry.QuaternionicTangentRootConversion
import Mathlib.Algebra.Algebra.Rat

/-! The finite triangular root recovery commutes with rational ring maps. -/
namespace QuaternionicSymmetry.QuaternionicRootRecoveryNaturality
open QuaternionicTangentRootConversion
noncomputable section
variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]

theorem map_recoveredStandardPower (f : R →+* S) (n : ℕ) (u : R)
    (t : ℕ → R) (j : Fin 7) :
    f (recoveredStandardPower n u t j) =
      recoveredStandardPower n (f u) (fun k => f (t k)) j := by
  fin_cases j <;> simp [recoveredStandardPower, recoveredSymplecticPowers,
    recoveredQ1, recoveredQ2, recoveredQ3, recoveredQ4, recoveredQ5, recoveredQ6,
    half, RingHom.map_rat_algebraMap, map_ofNat]

theorem recoveredStandardPower_congr_positive (n : ℕ) (u : R) (t s : ℕ → R)
    (h : ∀ m, 1 ≤ m → m ≤ 6 → t m = s m) (j : Fin 7) :
    recoveredStandardPower n u t j = recoveredStandardPower n u s j := by
  fin_cases j <;>
    simp [recoveredStandardPower, recoveredSymplecticPowers,
      recoveredQ1, recoveredQ2, recoveredQ3, recoveredQ4, recoveredQ5, recoveredQ6,
      h 1 (by omega) (by omega), h 2 (by omega) (by omega),
      h 3 (by omega) (by omega), h 4 (by omega) (by omega),
      h 5 (by omega) (by omega), h 6 (by omega) (by omega)]

end
end QuaternionicSymmetry.QuaternionicRootRecoveryNaturality
