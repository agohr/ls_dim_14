import QuaternionicSymmetry.ExteriorMatrixTraceBridge

/-! Every real matrix-valued continuous alternating two-form has a canonical
homogeneous exterior matrix, inverse to the matrix two-form pairing. -/
namespace QuaternionicSymmetry.ContinuousMatrixExteriorInverse
open ExteriorContinuousPairing ExteriorMatrixWedgeBridge
  QuaternionicExteriorEvenTrace EvenForms ContinuousMatrixWedgeEntries
noncomputable section

variable {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype κ] [DecidableEq κ]
local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

/-- Exterior coefficients of a real matrix-valued alternating two-form. -/
def exteriorMatrix (F : E [⋀^Fin 2]→L[ℝ] Matrix κ κ ℝ) :
    Matrix κ κ (EvenAlgebra E) :=
  fun i j => ofTwoForm ((equiv (V := E) 2).symm (entry i j F))

omit [Fintype κ] [DecidableEq κ] in
theorem entries_two (F : E [⋀^Fin 2]→L[ℝ] Matrix κ κ ℝ)
    (i j : κ) :
    ((exteriorMatrix F i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E) := by
  exact ((equiv (V := E) 2).symm (entry i j F)).property

/-- Pairing the canonical exterior matrix recovers the original
matrix-valued two-form exactly. -/
theorem matrixTwoForm_exteriorMatrix (F : E [⋀^Fin 2]→L[ℝ] Matrix κ κ ℝ) :
    matrixTwoForm (exteriorMatrix F) (entries_two F) = F := by
  apply ContinuousAlternatingMap.ext
  intro v
  ext i j
  change toContinuous 2 (powerEntry (exteriorMatrix F) (entries_two F) 1 i j) v =
    (entry i j F) v
  have he : powerEntry (exteriorMatrix F) (entries_two F) 1 i j =
      (equiv (V := E) 2).symm (entry i j F) := by
    apply Subtype.ext
    simp [powerEntry, exteriorMatrix, ofTwoForm_coe]
  rw [he]
  exact congrArg (fun α : E [⋀^Fin 2]→L[ℝ] ℝ => α v)
    ((equiv (V := E) 2).apply_symm_apply (entry i j F))

end
end QuaternionicSymmetry.ContinuousMatrixExteriorInverse
