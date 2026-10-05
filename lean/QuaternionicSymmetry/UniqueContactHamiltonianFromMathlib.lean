import QuaternionicSymmetry.GeneralFullContactHamiltonianSurjective
import QuaternionicSymmetry.HolomorphicKernelFamilyContact

/-! The original universal contact Hamiltonian contract, proved using the
retained closed-subgroup theorem and internally constructed holomorphic flows. -/
namespace QuaternionicSymmetry.UniqueContactHamiltonianFromMathlib
open GeneralUniqueContactHamiltonianSource GeneralClosedSubgroupLieSource
open GeneralContactComplexForm GeneralContactHamiltonianField
open GeneralHolomorphicFullAutomorphisms ManifoldTwistorLeBrunComplexAtlas
open scoped Manifold ContDiff
noncomputable section

theorem uniqueContactHamiltonian (hClosed : LeeClosedEmbeddingTheorem) :
    UniqueContactHamiltonianBijection := by
  intro R H Z V _ _ _ _ _ IR _ _ _ _ _ n hn C D hD
  intro hPres _ _ _ hChart hManifold hLie hJoint
  letI := C.charts
  letI := C.complexManifold
  letI := C.realManifold
  letI := C.lineHolomorphic
  letI := hChart
  letI := hManifold
  letI := hLie
  apply GeneralFullContactHamiltonianSurjective.fullHamiltonian_bijective_of_contact C hClosed hJoint
  intro v
  apply HolomorphicKernelFamilyContact.infinitesimal_isContact C.line (complexForm C)
    (complexForm_holomorphic C)
    (fun p : HolomorphicAutomorphisms (ComplexTwistorModel n) Z × Z => p.1.1 p.2)
    1 hJoint (fun x => rfl)
  intro g x w hw
  have hw' := (complexForm_apply C x w).symm.trans hw
  exact (complexForm_apply C (g.1 x) _).trans
    ((hD (g.1 x) _).mp ((hPres g).1 x w ((hD x w).mpr hw')))

end
end QuaternionicSymmetry.UniqueContactHamiltonianFromMathlib
