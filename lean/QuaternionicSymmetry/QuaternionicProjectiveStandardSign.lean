import QuaternionicSymmetry.QuaternionicProjectiveStandardAdjoint

/-! Two standard lifts of a tangent transition differ by a single central sign. -/
namespace QuaternionicSymmetry.QuaternionicProjectiveStandardSign
open QuaternionicProjectiveStandardAdjoint QuaternionicProjectiveStandardL2
  QuaternionicUnitScalarIsometries QuaternionicIsometryNormalizer
open scoped Quaternion
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E] (S : QuaternionicStructure E)

theorem standardActionL2_eq_or_neg_of_same_tangent
    (p r : symplecticKernel S × unitary ℍ)
    (h : symplecticProductAction S p = symplecticProductAction S r) :
    (standardActionL2 S p).toContinuousLinearMap =
      (standardActionL2 S r).toContinuousLinearMap ∨
    (standardActionL2 S p).toContinuousLinearMap =
      -(standardActionL2 S r).toContinuousLinearMap := by
  let d := p * r⁻¹
  have hd : symplecticProductAction S d = 1 := by
    dsimp [d]
    rw [map_mul, map_inv, h]
    group
  have hp : p = d * r := by dsimp [d]; group
  have hmul (z : StandardSpace (E := E)) :
      standardActionL2 S p z = standardActionL2 S d (standardActionL2 S r z) := by
    rw [hp]
    exact congrArg (fun T : StandardSpace (E := E) ≃ₗᵢ[ℝ]
      StandardSpace (E := E) => T z) (map_mul (standardIsometryL2 S) d r)
  rcases standardActionL2_kernel_sign S d hd with hpos | hneg
  · left
    ext z
    exact (hmul z).trans (hpos _)
  · right
    ext z
    exact (hmul z).trans (hneg _)

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardSign
