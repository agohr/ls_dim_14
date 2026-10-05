import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeCoreSection

/-! Applying an actual compact-symplectic element to the distinguished
identity coset gives precisely that element's coset. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorCosetActionBase

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticHomogeneousAtlasSource
open scoped Quaternion Matrix.Norms.Operator
noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem leftCosetAction_baseCoset (n : ℕ) (u : G n) :
    leftCosetAction n u (baseCoset n) = (u : ProjectiveCarrier n) := by
  letI : MulAction.QuotientAction (G n) (firstPairStabilizer n) :=
    MulAction.left_quotientAction (firstPairStabilizer n)
  letI : MulAction (G n) (ProjectiveCarrier n) :=
    MulAction.quotient (G n) (firstPairStabilizer n)
  change u • ((1 : G n) : ProjectiveCarrier n) = (u : ProjectiveCarrier n)
  simp only [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]

end
end QuaternionicSymmetry.CompactSymplecticProjectorCosetActionBase
