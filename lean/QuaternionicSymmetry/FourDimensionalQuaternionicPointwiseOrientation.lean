import QuaternionicSymmetry.FourDimensionalQuaternionicOrientation
import Mathlib.Analysis.Normed.Module.Normalize

/-! A quaternionic structure on one real four-dimensional inner-product
space induces a choice-independent orientation of that *single* space.
Transport across tangent adapted charts is a further manifold-level theorem. -/
namespace QuaternionicSymmetry.FourDimensionalQuaternionicPointwiseOrientation

open FourDimensionalQuaternionicHodgeFrame
open FourDimensionalQuaternionicOrientation
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

private def chosenNonzero : V := Classical.choose (exists_ne (0 : V))

private theorem chosenNonzero_ne_zero : (chosenNonzero : V) ≠ 0 :=
  Classical.choose_spec (exists_ne (0 : V))

private def chosenUnit : V := NormedSpace.normalize (chosenNonzero : V)

private theorem chosenUnit_norm : ‖(chosenUnit : V)‖ = 1 :=
  NormedSpace.norm_normalize chosenNonzero_ne_zero

def pointwiseQuaternionicOrientation (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) : Orientation ℝ V (Fin 4) :=
  (frameBasis Q hdim chosenUnit chosenUnit_norm).toBasis.orientation

theorem frame_has_pointwiseQuaternionicOrientation (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    (frameBasis Q hdim v hv).toBasis.orientation =
      pointwiseQuaternionicOrientation Q hdim :=
  frame_orientation_eq Q hdim v chosenUnit hv chosenUnit_norm

end
end QuaternionicSymmetry.FourDimensionalQuaternionicPointwiseOrientation
