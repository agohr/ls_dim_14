import QuaternionicSymmetry.FourDimensionalExteriorHodge
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The natural finite-dimensional topology on genuine exterior two-covectors
in real dimension four. It is induced by six evaluations in one basis, then
proved independent of that basis through a continuous linear coordinate
change. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorTwoFormTopology

open Module FourDimensionalExteriorHodge
open FourDimensionalCoordinateHodge
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def twoFormTopology (b : Basis (Fin 4) ℝ V) : TopologicalSpace (TwoForm V) :=
  TopologicalSpace.induced (coordinates b) inferInstance

def coordinateChange (b c : Basis (Fin 4) ℝ V) : Two →ₗ[ℝ] Two :=
  (coordinates c).comp (reconstruct b)

theorem coordinateChange_apply (b c : Basis (Fin 4) ℝ V)
    (α : TwoForm V) :
    coordinateChange b c (coordinates b α) = coordinates c α := by
  simp [coordinateChange]

theorem coordinateChange_continuous (b c : Basis (Fin 4) ℝ V) :
    Continuous (coordinateChange b c) :=
  (coordinateChange b c).continuous_of_finiteDimensional

theorem continuous_coordinates_from (b c : Basis (Fin 4) ℝ V) :
    @Continuous (TwoForm V) Two (twoFormTopology b) inferInstance
      (coordinates c) := by
  letI : TopologicalSpace (TwoForm V) := twoFormTopology b
  have hcomp : (fun α : TwoForm V => coordinates c α) =
      (fun α => coordinateChange b c (coordinates b α)) := by
    funext α
    exact (coordinateChange_apply b c α).symm
  change Continuous (fun α : TwoForm V => coordinates c α)
  rw [hcomp]
  exact (coordinateChange_continuous b c).comp continuous_induced_dom

theorem twoFormTopology_basis_independent
    (b c : Basis (Fin 4) ℝ V) :
    twoFormTopology b = twoFormTopology c := by
  apply le_antisymm
  · apply continuous_id_iff_le.mp
    apply continuous_induced_rng.mpr
    exact continuous_coordinates_from b c
  · apply continuous_id_iff_le.mp
    apply continuous_induced_rng.mpr
    exact continuous_coordinates_from c b

end
end QuaternionicSymmetry.FourDimensionalExteriorTwoFormTopology
