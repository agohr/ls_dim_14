import QuaternionicSymmetry.ComplexProjectiveProjCutoutComparison

/-! Every relevant homogeneous prime has a nonzero complex zero on its
affine cone. Closed-point surjectivity will then use specialization. -/

namespace QuaternionicSymmetry.ComplexProjectiveProjClosedPoints

open ComplexProjectiveTopology
open ComplexProjectiveLineProjPoint
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

theorem eval_zero_of_mem_irrelevant
    {p : MvPolynomial (Fin (d + 1)) ℂ}
    (hp : p ∈ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)) :
    MvPolynomial.eval (0 : Coord d) p = 0 := by
  have hcomp : MvPolynomial.homogeneousComponent 0 p = 0 := by
    change ((DirectSum.decompose
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) p 0 :
        MvPolynomial (Fin (d + 1)) ℂ)) = 0 at hp
    change ((MvPolynomial.decomposition.decompose' p 0 :
      MvPolynomial (Fin (d + 1)) ℂ)) = 0 at hp
    rwa [MvPolynomial.decomposition.decompose'_apply] at hp
  rw [MvPolynomial.homogeneousComponent_zero] at hcomp
  have hc := congrArg MvPolynomial.constantCoeff hcomp
  simpa [MvPolynomial.eval_zero] using hc

theorem exists_nonzero_zero_of_relevant
    (q : ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)) :
    ∃ v : Coord d, v ≠ 0 ∧
      v ∈ MvPolynomial.zeroLocus ℂ q.asHomogeneousIdeal.toIdeal := by
  by_contra hno
  push_neg at hno
  have hzero (v : Coord d)
      (hv : v ∈ MvPolynomial.zeroLocus ℂ q.asHomogeneousIdeal.toIdeal) : v = 0 := by
    by_contra hv0
    exact hno v hv0 hv
  have hbad : HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) ≤
      q.asHomogeneousIdeal := by
    intro p hp
    have hVan : p ∈ MvPolynomial.vanishingIdeal ℂ
        (MvPolynomial.zeroLocus ℂ q.asHomogeneousIdeal.toIdeal) := by
      intro v hv
      have hv0 := hzero v hv
      subst v
      simpa only [MvPolynomial.aeval_eq_eval] using
        eval_zero_of_mem_irrelevant hp
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical,
      q.isPrime.radical] at hVan
    exact hVan
  exact q.not_irrelevant_le hbad

end
end QuaternionicSymmetry.ComplexProjectiveProjClosedPoints
