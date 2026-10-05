import QuaternionicSymmetry.NonzeroRootSpaceDimensionBound

/-! The nonzero-root restriction is essential even for the Cartan setup used
by the actual torus argument: the zero root space has the Cartan dimension.
This regression prevents extending the one-dimensional bound to zero. -/

namespace QuaternionicSymmetry.ZeroRootMultiplicityRegression

open LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

theorem zero_root_finrank_eq_cartan :
    Module.finrank ℂ (rootSpace H (0 : H → ℂ)) = Module.finrank ℂ H := by
  rw [rootSpace_zero_eq]
  rfl

/-- At rank at least two, an alleged bound for every root, including zero,
contradicts the actual Cartan zero-root-space identity. -/
theorem root_bound_cannot_include_zero (hRank : 2 ≤ Module.finrank ℂ H) :
    ¬ ∀ α : H → ℂ, Module.finrank ℂ (rootSpace H α) ≤ 1 := by
  intro hBound
  have hZero := hBound 0
  rw [zero_root_finrank_eq_cartan H] at hZero
  omega

end QuaternionicSymmetry.ZeroRootMultiplicityRegression
