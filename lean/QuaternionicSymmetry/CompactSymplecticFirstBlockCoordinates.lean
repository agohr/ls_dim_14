import QuaternionicSymmetry.CompactSymplecticStabilizerBlockSurjection

/-! The first two-dimensional block is the usual `Sp(1)` matrix model,
not an independently postulated compact group. -/

namespace QuaternionicSymmetry.CompactSymplecticFirstBlockCoordinates

open Matrix CompactSymplecticHaar
open CompactSymplecticStabilizerFormBlocks
noncomputable section

def pairIndexEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin 2 where
  toFun
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  invFun := Fin.cases (Sum.inl 0) (fun _ => Sum.inr 0)
  left_inv := by
    intro i
    rcases i with i | i <;> fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem firstBlockJ_eq_reindex_standardJ_one :
    firstBlockJ = (standardJ 1).reindex pairIndexEquiv pairIndexEquiv := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstBlockJ, CompactSymplecticStabilizerFormBlocks.blockStandardJ,
      CompactSymplecticStabilizerIndex.blockIndexEquiv, pairIndexEquiv,
      standardJ, Matrix.toBlocks₁₁, Matrix.fromBlocks,
      Matrix.reindex_apply]

end
end QuaternionicSymmetry.CompactSymplecticFirstBlockCoordinates
