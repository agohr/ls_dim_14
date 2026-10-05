import QuaternionicSymmetry.CompactSymplecticProjectorStabilizerFiberLinear

/-! The moved complex line is independent of replacing its symplectic
representative by a first-pair stabilizer element, provided the fiber
coordinate is transformed by the checked first Sp(1) block. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorAssociatedDescentLinear

open Matrix CompactSymplecticProjectorTwistorGroupFiberLinear
open CompactSymplecticProjectorStabilizerFiberLinear
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticStabilizerBlockPair

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) :=
  CompactSymplecticProjectiveQuotient.firstPairStabilizer n

theorem fiberLineMap_stabilizer_independent (n : ℕ)
    (u : G n) (k : K n) (z : Fin 2 → ℂ) :
    fiberLineMap n (firstColumnSphere n (u * (k⁻¹ : G n)))
      (((blockPair n k).1.1.1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z) =
      fiberLineMap n (firstColumnSphere n u) z := by
  rw [fiberLineMap_eq_mulVec_firstPair, fiberLineMap_eq_mulVec_firstPair]
  rw [← stabilizer_mulVec_firstPair n k z]
  change (((u * (k⁻¹ : G n)).1.1 : Matrix (I n) (I n) ℂ) *ᵥ
      (((k : G n).1.1 : Matrix (I n) (I n) ℂ) *ᵥ firstPairEmbedding n z)) =
    ((u.1.1 : Matrix (I n) (I n) ℂ) *ᵥ firstPairEmbedding n z)
  rw [Matrix.mulVec_mulVec]
  change (((u * (k⁻¹ : G n)) * (k : G n)).1.1 :
    Matrix (I n) (I n) ℂ) *ᵥ firstPairEmbedding n z = _
  simp

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorAssociatedDescentLinear
