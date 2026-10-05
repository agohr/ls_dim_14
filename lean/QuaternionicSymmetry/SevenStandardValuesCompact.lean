import QuaternionicSymmetry.RecoveredLogAhatSix

namespace QuaternionicSymmetry.SevenStandardValuesCompact
open RecoveredLogAhatSix QuaternionicTangentRootConversion
noncomputable section

variable {R : Type} [CommRing R] [Algebra ℚ R]

theorem standardValues_eq (n : ℕ) (u : R) (t : ℕ → R) :
    standardValues n u t =
      fun i : Fin 7 => if i = 0 then u else recoveredStandardPower n u t i := by
  funext i
  fin_cases i <;> rfl

end
end QuaternionicSymmetry.SevenStandardValuesCompact
