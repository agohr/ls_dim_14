import QuaternionicSymmetry.TorusLaurentRepresentation
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! The finite product of complex units has its standard complex-smooth
manifold structure. -/

namespace QuaternionicSymmetry.ComplexTorusHolomorphicStructure

open TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

def torusVal (r : ℕ) : ComplexTorus r → (Fin r → ℂ) :=
  fun z i => z i

theorem torusVal_isOpenEmbedding (r : ℕ) :
    Topology.IsOpenEmbedding (torusVal r) := by
  simpa [torusVal, Pi.map] using
    (Topology.IsOpenEmbedding.piMap
      (fun _ : Fin r => Units.isOpenEmbedding_val))

noncomputable instance (r : ℕ) :
    ChartedSpace (Fin r → ℂ) (ComplexTorus r) :=
  (torusVal_isOpenEmbedding r).singletonChartedSpace

noncomputable instance (r : ℕ) :
    IsManifold 𝓘(ℂ, Fin r → ℂ) ∞ (ComplexTorus r) :=
  (torusVal_isOpenEmbedding r).isManifold_singleton

end
end QuaternionicSymmetry.ComplexTorusHolomorphicStructure
