import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedCorrectedHopf
import QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberLine
import QuaternionicSymmetry.CompactSymplecticProjectorFirstColumnUnit

/-! The concrete complex two-plane over a group representative is exactly
the image of the standard first-pair complex plane under that symplectic
matrix. This is the linear identity behind the associated-CP¹ comparison. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorGroupFiberLinear

open Matrix CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnPhase
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorFirstColumnUnit

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def firstPairEmbedding (n : ℕ) : (Fin 2 → ℂ) →ₗ[ℂ] V n where
  toFun z := fun i => match i with
    | Sum.inl j => if j = 0 then z 0 else 0
    | Sum.inr j => if j = 0 then z 1 else 0
  map_add' := by
    intro z w
    funext i
    cases i with
    | inl j => by_cases h : j = 0 <;> simp [h]
    | inr j => by_cases h : j = 0 <;> simp [h]
  map_smul' := by
    intro c z
    funext i
    cases i with
    | inl j => by_cases h : j = 0 <;> simp [h]
    | inr j => by_cases h : j = 0 <;> simp [h]

theorem firstPairEmbedding_injective (n : ℕ) :
    Function.Injective (firstPairEmbedding n) := by
  intro z w h
  funext i
  fin_cases i
  · have hh := congrFun h (Sum.inl (0 : Fin (n + 1)))
    simpa [firstPairEmbedding] using hh
  · have hh := congrFun h (Sum.inr (0 : Fin (n + 1)))
    simpa [firstPairEmbedding] using hh

theorem fiberLineMap_eq_mulVec_firstPair (n : ℕ) (u : G n)
    (z : Fin 2 → ℂ) :
    fiberLineMap n (firstColumnSphere n u) z =
      (u.1.1 : Matrix (I n) (I n) ℂ) *ᵥ firstPairEmbedding n z := by
  funext i
  simp only [fiberLineMap, LinearMap.coe_mk, AddHom.coe_mk,
    firstColumnSphere, firstColumnEuclidean, phaseRotate, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, pairedColumn]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    firstPairEmbedding, Fin.sum_univ_succ]
  cases i with
  | inl j => simp [firstColumn, first_pair_column_inl, mul_comm]
  | inr j => simp [firstColumn, first_pair_column_inr, mul_comm]

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorGroupFiberLinear
