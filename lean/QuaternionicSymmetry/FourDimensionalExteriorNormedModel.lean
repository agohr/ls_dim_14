import QuaternionicSymmetry.FourDimensionalExteriorTwoFormCanonicalTopology
import Mathlib.Analysis.Normed.Module.Basic

/-! A real normed model of genuine exterior two-covectors transported from
the six-coordinate Euclidean product by an actual linear equivalence. The
resulting topology is proved to equal the previously established canonical
basis-independent topology. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorNormedModel

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorTwoFormCanonicalTopology
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def normedAddCommGroup (hdim : Module.finrank ℝ V = 4) :
    NormedAddCommGroup (TwoForm V) :=
  NormedAddCommGroup.induced (TwoForm V)
    FourDimensionalCoordinateHodge.Two
    (coordinates (canonicalBasis hdim))
    (coordinateEquiv (canonicalBasis hdim)).injective

def normedSpace (hdim : Module.finrank ℝ V = 4) :
    @NormedSpace ℝ (TwoForm V) _
      (normedAddCommGroup hdim).toSeminormedAddCommGroup :=
  NormedSpace.induced ℝ (TwoForm V)
    FourDimensionalCoordinateHodge.Two (coordinates (canonicalBasis hdim))

def normedTopology (hdim : Module.finrank ℝ V = 4) :
    TopologicalSpace (TwoForm V) := by
  letI : NormedAddCommGroup (TwoForm V) := normedAddCommGroup hdim
  infer_instance

theorem normed_topology_eq (hdim : Module.finrank ℝ V = 4) :
    normedTopology hdim =
    canonicalTwoFormTopology hdim := by
  rfl

end
end QuaternionicSymmetry.FourDimensionalExteriorNormedModel
