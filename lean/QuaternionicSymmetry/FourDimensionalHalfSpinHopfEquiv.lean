import QuaternionicSymmetry.FourDimensionalHalfSpinHopfInjective

/-! A genuine explicit bijection from the true complex projective
half-spin line to the coefficient two-sphere, built from the explicit Hopf
formula and proved injectivity/surjectivity.  Topological and smooth
equivalence, and global associated-bundle matching, remain separate. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfEquiv

open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfInjective
  FourDimensionalHalfSpinHopfSurjective
open ManifoldTwistorSphereBundle

noncomputable section

def projectiveHopfEquiv : ProjectiveSpinor ≃ coefficientSphere :=
  Equiv.ofBijective projectiveHopf
    ⟨projectiveHopf_injective, projectiveHopf_surjective⟩

@[simp] theorem projectiveHopfEquiv_apply (p : ProjectiveSpinor) :
    projectiveHopfEquiv p = projectiveHopf p := rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfEquiv
