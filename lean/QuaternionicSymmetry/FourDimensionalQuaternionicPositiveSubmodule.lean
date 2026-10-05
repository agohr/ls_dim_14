import QuaternionicSymmetry.FourDimensionalQuaternionicPositiveHalf
import QuaternionicSymmetry.VectorBundleFrameTransitions

/-! The project-native quaternionic endomorphism submodule maps exactly onto
the Hodge-positive two-form coefficient submodule in every unit Q-frame. -/
namespace QuaternionicSymmetry.FourDimensionalQuaternionicPositiveSubmodule

open FourDimensionalCoordinateHodge FourDimensionalQuaternionicHodgeFrame
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def twoCoordsLinear (b : OrthonormalBasis (Fin 4) ℝ V) :
    (V →L[ℝ] V) →ₗ[ℝ] Two where
  toFun A := operatorTwoCoords b A.toLinearMap
  map_add' A B := by
    funext i
    fin_cases i <;> simp [operatorTwoCoords, Pi.add_apply, inner_add_left]
  map_smul' a A := by
    funext i
    fin_cases i <;> simp [operatorTwoCoords, Pi.smul_apply, inner_smul_left]

def positiveHalf : Submodule ℝ Two :=
  LinearMap.ker (star - LinearMap.id)

theorem mem_positiveHalf (x : Two) :
    x ∈ positiveHalf ↔ FourDimensionalCoordinateHodge.star x = x := by
  simp [positiveHalf, LinearMap.mem_ker, sub_eq_zero]

theorem generator_coordinates (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1)
    (t : Fin 3) :
    twoCoordsLinear (frameBasis Q hdim v hv) (quaternionicGenerator Q t) =
      ![plusI, plusJ, plusK] t := by
  fin_cases t
  · simpa [twoCoordsLinear, quaternionicGenerator] using I_coordinates Q hdim v hv
  · simpa [twoCoordsLinear, quaternionicGenerator] using J_coordinates Q hdim v hv
  · simpa [twoCoordsLinear, quaternionicGenerator] using K_coordinates Q hdim v hv

theorem quaternionicSpan_maps_into_positiveHalf (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    (quaternionicSpan Q).map (twoCoordsLinear (frameBasis Q hdim v hv)) ≤
      positiveHalf := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro A ⟨t, rfl⟩
  change twoCoordsLinear (frameBasis Q hdim v hv)
    (quaternionicGenerator Q t) ∈ positiveHalf
  rw [mem_positiveHalf]
  change FourDimensionalCoordinateHodge.star (twoCoordsLinear (frameBasis Q hdim v hv)
    (quaternionicGenerator Q t)) =
    twoCoordsLinear (frameBasis Q hdim v hv) (quaternionicGenerator Q t)
  rw [generator_coordinates]
  fin_cases t <;> simp [star_plusI, star_plusJ, star_plusK]

theorem positiveHalf_le_quaternionicSpan_image (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    positiveHalf ≤
      (quaternionicSpan Q).map (twoCoordsLinear (frameBasis Q hdim v hv)) := by
  intro x hx
  have hx' := (mem_positiveHalf x).mp hx
  obtain ⟨a, b, c, h⟩ :=
    (FourDimensionalQuaternionicPositiveHalf.positive_iff_quaternionic_span
      Q hdim v hv x).mp hx'
  let A := a • quaternionicGenerator Q 0 +
    b • quaternionicGenerator Q 1 + c • quaternionicGenerator Q 2
  have hA : A ∈ quaternionicSpan Q := by
    exact (quaternionicSpan Q).add_mem
      ((quaternionicSpan Q).add_mem
        ((quaternionicSpan Q).smul_mem a (generator_mem_span Q 0))
        ((quaternionicSpan Q).smul_mem b (generator_mem_span Q 1)))
      ((quaternionicSpan Q).smul_mem c (generator_mem_span Q 2))
  refine ⟨A, hA, ?_⟩
  rw [I_coordinates, J_coordinates, K_coordinates] at h
  simpa [A, generator_coordinates] using h.symm

theorem positiveHalf_eq_quaternionicSpan_image (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    positiveHalf =
      (quaternionicSpan Q).map (twoCoordsLinear (frameBasis Q hdim v hv)) := by
  exact le_antisymm
    (positiveHalf_le_quaternionicSpan_image Q hdim v hv)
    (quaternionicSpan_maps_into_positiveHalf Q hdim v hv)

end
end QuaternionicSymmetry.FourDimensionalQuaternionicPositiveSubmodule
