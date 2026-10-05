import QuaternionicSymmetry.ComplexProjectiveProjClassicalClosed

/-! A literal equivalence of sets between actual complex projective
points and the Zariski-closed points of Mathlib's standard Proj. This
does not assert an equivalence of topological or smooth spaces. -/

namespace QuaternionicSymmetry.ComplexProjectiveProjClosedPointEquiv

open ComplexProjectiveTopology
open ComplexProjectiveLineProjPoint ComplexProjectiveLineProjInjective
open ComplexProjectiveProjClosedSurjection ComplexProjectiveProjClassicalClosed
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

abbrev ClosedProjPoint (d : ℕ) :=
  {q : ProjectiveSpectrum
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) // IsClosed {q}}

def projectiveClosedPointEquiv : Space d ≃ ClosedProjPoint d :=
  Equiv.ofBijective
    (fun x => (⟨projectivePointToProj x,
      projectivePointToProj_isClosed x⟩ : ClosedProjPoint d))
    ⟨fun x y h => projectivePointToProj_injective (congrArg Subtype.val h),
      by
        intro q
        obtain ⟨x,hx⟩ := projectivePointToProj_surjective_on_closed_points
          q.1 q.2
        exact ⟨x, Subtype.ext hx⟩⟩

end
end QuaternionicSymmetry.ComplexProjectiveProjClosedPointEquiv
