import QuaternionicSymmetry.CompactSymplecticProjectorBaseOrthonormalCoordinates
import QuaternionicSymmetry.QuaternionicStructureIsometryTransport

/-! The actual row-model quaternionic structure, expressed in the real
Euclidean fiber selected for the genuine quotient's tangent atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseStandardQuaternionicStructure

open CompactSymplecticProjectorBaseOrthonormalCoordinates
open QuaternionicStructureIsometryTransport
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def standardRealQuaternionicStructure (n q : ℕ) (hq : q = 4 * n) :
    QuaternionicStructure (EModel q) :=
  transport (QuaternionicMatrixModel.standardQuaternionicStructure n)
    (standardQuaternionicRealCoordinates n q hq)

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseStandardQuaternionicStructure
