import QuaternionicSymmetry.ComplexProjectiveRealManifold
import Mathlib.Topology.Bases

/-! Finite affine-chart cover makes the literal projective quotient
second-countable. -/

namespace QuaternionicSymmetry.ComplexProjectiveTopology

noncomputable section

instance (d : ℕ) : SecondCountableTopology (Space d) := by
  letI (i : Fin (d + 1)) : SecondCountableTopology (affineDomain d i) :=
    (affineEuclideanHomeomorph d i).secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := affineDomain d) (fun i => isOpen_affineDomain d i)
  ext p
  simpa only [Set.mem_iUnion, Set.mem_univ, iff_true] using
    exists_mem_affineDomain d p

end
end QuaternionicSymmetry.ComplexProjectiveTopology
