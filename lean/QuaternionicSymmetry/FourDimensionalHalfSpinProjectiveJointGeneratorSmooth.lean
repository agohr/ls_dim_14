import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGenerator

/-! The polynomial infinitesimal projective action is jointly smooth in
its actual matrix and affine coordinate arguments. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointGeneratorSmooth

open scoped ContDiff Matrix
open FourDimensionalHalfSpinProjectiveGenerator

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

private theorem matrixEntry_smooth (i j : Fin 2) :
    ContDiff ℝ ∞ (fun A : Mat2 => A i j) := by
  let L : Mat2 →ₗ[ℝ] ℂ :=
    { toFun := fun A => A i j
      map_add' := by intro A B; rfl
      map_smul' := by intro c A; rfl }
  exact (⟨L, L.continuous_of_finiteDimensional⟩ : Mat2 →L[ℝ] ℂ).contDiff

private theorem pairEntry_smooth (i j : Fin 2) :
    ContDiff ℝ ∞ (fun Az : Mat2 × ℂ => Az.1 i j) :=
  (matrixEntry_smooth i j).comp contDiff_fst

theorem affineGenerator_smooth :
    ContDiff ℝ ∞ (fun Az : Mat2 × ℂ => affineGenerator Az.1 Az.2) := by
  have h00 := pairEntry_smooth 0 0
  have h01 := pairEntry_smooth 0 1
  have h10 := pairEntry_smooth 1 0
  have h11 := pairEntry_smooth 1 1
  change ContDiff ℝ ∞ (fun Az : Mat2 × ℂ =>
    Az.1 1 0 + (Az.1 1 1 - Az.1 0 0) * Az.2 - Az.1 0 1 * Az.2 ^ 2)
  exact (h10.add ((h11.sub h00).mul contDiff_snd)).sub
    (h01.mul (contDiff_snd.pow 2))

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveJointGeneratorSmooth
