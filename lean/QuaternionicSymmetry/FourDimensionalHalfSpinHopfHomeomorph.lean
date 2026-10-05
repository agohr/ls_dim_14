import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCompact

/-! The explicit projective Hopf bijection is a homeomorphism for the
independently given canonical quotient topology on `CP¹` and Euclidean
subspace topology on the coefficient sphere.  Neither topology is
transported from the other. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfHomeomorph

open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfEquiv
  FourDimensionalHalfSpinHopfContinuous
open ManifoldTwistorSphereBundle

noncomputable section

local instance : T2Space coefficientSphere := by
  unfold coefficientSphere
  infer_instance

def projectiveHopfHomeomorph : ProjectiveSpinor ≃ₜ coefficientSphere :=
  projectiveHopf_continuous.homeoOfEquivCompactToT2
    (f := projectiveHopfEquiv)

@[simp] theorem projectiveHopfHomeomorph_apply (p : ProjectiveSpinor) :
    projectiveHopfHomeomorph p =
      FourDimensionalHalfSpinHopfProjectiveDescent.projectiveHopf p := by
  change projectiveHopfEquiv p = _
  rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfHomeomorph
