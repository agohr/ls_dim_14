import QuaternionicSymmetry.CompactSymplecticFirstBlockGroup

/-! The actual projector stabilizer is, by checked matrix algebra and
explicit finite-coordinate changes, exactly `Sp(1) × Sp(n)` as a group.
The Lie-atlas/dimension compatibility is a separate task. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerProduct

open CompactSymplecticProjectiveQuotient
open CompactSymplecticStabilizerBlockSurjection
open CompactSymplecticFirstBlockGroup
noncomputable section

/-- No bespoke classification premise: the two factors are the actual
Mathlib-matrix compact symplectic groups already used elsewhere. -/
def stabilizerProductEquiv (n : ℕ) :
    firstPairStabilizer n ≃*
      CompactSymplecticHaar.Group 1 × CompactSymplecticHaar.Group n :=
  (stabilizerBlockProductEquiv n).trans
    (MulEquiv.prodCongr firstBlockGroupEquiv.symm
      (MulEquiv.refl (CompactSymplecticHaar.Group n)))

end
end QuaternionicSymmetry.CompactSymplecticStabilizerProduct
