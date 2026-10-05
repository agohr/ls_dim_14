import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! A subspace contained in a nonzero root space has dimension at most
one. This is an internal application of mathlib's Killing/Cartan root
theorem. The actual geometric Cartan and Killing hypotheses are not
supplied by this file. -/

namespace QuaternionicSymmetry.NonzeroRootSpaceDimensionBound

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  [FiniteDimensional ℂ L] [LieAlgebra.IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

theorem finrank_le_one_of_le_nonzero_rootSpace
    (W : Submodule ℂ L) (α : H → ℂ) (hα : α ≠ 0)
    (hW : W ≤ (LieAlgebra.rootSpace H α).toSubmodule) :
    Module.finrank ℂ W ≤ 1 := by
  classical
  by_cases hRoot : LieAlgebra.rootSpace H α = ⊥
  · have hZero : W = ⊥ := by
      apply le_antisymm _ bot_le
      simpa [hRoot] using hW
    subst W
    simp
  · let χ : Weight ℂ H L := ⟨α,hRoot⟩
    have hχ : χ.IsNonZero := hα
    have hDim := LieAlgebra.IsKilling.finrank_rootSpace_eq_one χ hχ
    exact (Submodule.finrank_mono hW).trans hDim.le

end QuaternionicSymmetry.NonzeroRootSpaceDimensionBound
