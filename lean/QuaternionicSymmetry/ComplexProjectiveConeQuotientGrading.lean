import QuaternionicSymmetry.ComplexProjectiveConeQuotientHomogeneousPieces

/-! A genuine Mathlib graded-algebra structure on the actual homogeneous
cone quotient, constructed from its literal vanishing ideal. The
homogeneous-equation and nonemptiness hypotheses are used only to prove
degree-piece independence. -/

namespace QuaternionicSymmetry.ComplexProjectiveConeQuotientGrading

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
noncomputable section

variable {d : ℕ}

instance quotientPiece_gradedMonoid (A : Set (Space d)) :
    SetLike.GradedMonoid (quotientPiece A) where
  one_mem := one_mem_quotientPiece_zero A
  mul_mem _ _ _ _ := mul_mem_quotientPiece A

def quotientGradedAlgebra (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    GradedAlgebra (quotientPiece A) :=
  DirectSum.IsInternal.gradedAlgebra
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (quotientPiece_iSupIndep A hA hNonempty)
      (iSup_quotientPiece_eq_top A))

end
end QuaternionicSymmetry.ComplexProjectiveConeQuotientGrading
