import QuaternionicSymmetry.ContinuousMatrixExteriorEquivalence
import QuaternionicSymmetry.HomogeneousMatrixCombinations

/-! A finite real matrix combination with homogeneous exterior
two-form coefficients pairs to the corresponding matrix-valued
continuous alternating form. -/
namespace QuaternionicSymmetry.ContinuousMatrixCombinationPairing
open ExteriorContinuousPairing ExteriorMatrixWedgeBridge
  QuaternionicExteriorEvenTrace EvenForms RealifiedTracePolynomial
  HomogeneousMatrixCombinations ContinuousMatrixWedgeEntries
noncomputable section
set_option maxHeartbeats 1000000

variable {E κ β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype κ] [DecidableEq κ] [Fintype β]
local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

def formCombination (B : β → Matrix κ κ ℝ)
    (ω : β → E [⋀^Fin 2]→L[ℝ] ℝ) :
    E [⋀^Fin 2]→L[ℝ] Matrix κ κ ℝ :=
  ContinuousAlternatingMap.pi (fun i : κ =>
    ContinuousAlternatingMap.pi (fun j : κ =>
      ∑ a, (B a i j) • ω a))

omit [FiniteDimensional ℝ E] [Fintype κ] [DecidableEq κ] in
@[simp] theorem formCombination_apply (B : β → Matrix κ κ ℝ)
    (ω : β → E [⋀^Fin 2]→L[ℝ] ℝ) (v : Fin 2 → E) (i j : κ) :
    formCombination B ω v i j = (∑ a, (B a i j) • ω a) v := by
  rfl

theorem matrixTwoForm_combination (B : β → Matrix κ κ ℝ)
    (ω : β → Power E 2) :
    matrixTwoForm (combination B (fun a => ofTwoForm (ω a)))
      (combination_entries_two B _ (fun a => (ω a).property)) =
      formCombination B (fun a => toContinuous 2 (ω a)) := by
  apply ContinuousAlternatingMap.ext
  intro v
  apply Matrix.ext
  intro i j
  change toContinuous 2
    (powerEntry (combination B (fun a => ofTwoForm (ω a)))
      (combination_entries_two B _ (fun a => (ω a).property)) 1 i j) v =
    (∑ a, (B a i j) • toContinuous 2 (ω a)) v
  have hpow : powerEntry (combination B (fun a => ofTwoForm (ω a)))
      (combination_entries_two B _ (fun a => (ω a).property)) 1 i j =
      ∑ a, (B a i j) • ω a := by
    apply Subtype.ext
    simp [powerEntry, combination, ofTwoForm_coe, Algebra.smul_def]
  rw [hpow]
  simp only [ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply]
  have hmap : toContinuous 2 (∑ a, (B a i j) • ω a) =
      ∑ a, (B a i j) • toContinuous 2 (ω a) := by
    change (toContinuousLinear (V := E) 2)
      (∑ a, (B a i j) • ω a) =
        ∑ a, (B a i j) • (toContinuousLinear (V := E) 2) (ω a)
    simp only [map_sum, map_smul]
  simpa only [ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply] using
      congrArg (fun f : E [⋀^Fin 2]→L[ℝ] ℝ => f v) hmap

end
end QuaternionicSymmetry.ContinuousMatrixCombinationPairing
