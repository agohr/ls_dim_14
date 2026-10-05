import QuaternionicSymmetry.ContinuousMatrixExteriorInverse

/-! The matrix exterior encoding and its continuous two-form pairing are
inverse on entrywise homogeneous matrices. -/
namespace QuaternionicSymmetry.ContinuousMatrixExteriorEquivalence
open ContinuousMatrixExteriorInverse ExteriorMatrixWedgeBridge
  ExteriorContinuousPairing ExteriorMatrixTraceBridge
  QuaternionicExteriorEvenTrace EvenForms
noncomputable section

variable {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype κ] [DecidableEq κ]
local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

theorem matrixTwoForm_congr (A B : Matrix κ κ (EvenAlgebra E))
    (hA : ∀ i j, ((A i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (hB : ∀ i j, ((B i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (h : A = B) : matrixTwoForm A hA = matrixTwoForm B hB := by
  subst B
  rfl

omit [FiniteDimensional ℝ E] in
theorem wedgeTrace_congr (A B : Matrix κ κ (EvenAlgebra E))
    (hA : ∀ i j, ((A i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (hB : ∀ i j, ((B i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (k : ℕ) (h : A = B) : wedgeTrace A hA k = wedgeTrace B hB k := by
  subst B
  rfl

omit [FiniteDimensional ℝ E] [Fintype κ] [DecidableEq κ] in
theorem entries_two_add (A B : Matrix κ κ (EvenAlgebra E))
    (hA : ∀ i j, ((A i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (hB : ∀ i j, ((B i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (i j : κ) :
    (((A + B) i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E) :=
  (ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E)).add_mem
    (hA i j) (hB i j)

theorem matrixTwoForm_add (A B : Matrix κ κ (EvenAlgebra E))
    (hA : ∀ i j, ((A i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (hB : ∀ i j, ((B i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E)) :
    matrixTwoForm (A + B) (entries_two_add A B hA hB) =
      matrixTwoForm A hA + matrixTwoForm B hB := by
  apply ContinuousAlternatingMap.ext
  intro v
  apply Matrix.ext
  intro i j
  change toContinuous 2 (powerEntry (A+B) (entries_two_add A B hA hB) 1 i j) v =
    toContinuous 2 (powerEntry A hA 1 i j) v +
      toContinuous 2 (powerEntry B hB 1 i j) v
  have hp : powerEntry (A+B) (entries_two_add A B hA hB) 1 i j =
      powerEntry A hA 1 i j + powerEntry B hB 1 i j := by
    apply Subtype.ext
    simp [powerEntry, Matrix.add_apply]
  rw [hp, toContinuous_add]
  rfl

theorem exteriorMatrix_matrixTwoForm (A : Matrix κ κ (EvenAlgebra E))
    (hA : ∀ i j, ((A i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E)) :
    exteriorMatrix (matrixTwoForm A hA) = A := by
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  change (((equiv (V := E) 2).symm
    (toContinuous 2 (powerEntry A hA 1 i j)) : Power E 2) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) = _
  change (((equiv (V := E) 2).symm
    ((equiv (V := E) 2) (powerEntry A hA 1 i j)) : Power E 2) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) = _
  rw [(equiv (V := E) 2).symm_apply_apply]
  simp [powerEntry]

end
end QuaternionicSymmetry.ContinuousMatrixExteriorEquivalence
