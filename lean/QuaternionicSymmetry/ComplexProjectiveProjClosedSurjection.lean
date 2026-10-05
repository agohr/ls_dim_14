import QuaternionicSymmetry.ComplexProjectiveProjClosedPoints

/-! Every closed point of the standard complex projective spectrum comes
from an actual complex projective line. Nonclosed generic Proj points are
not asserted to be classical projective points. -/

namespace QuaternionicSymmetry.ComplexProjectiveProjClosedSurjection

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveLineProjPoint ComplexProjectiveLineProjLocus
open ComplexProjectiveLineKernelHomogeneous
open ComplexProjectiveProjClosedPoints
open scoped LinearAlgebra.Projectivization Polynomial
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

theorem homogeneousPrime_le_linePrimeIdeal
    (q : ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ))
    (v : Coord d)
    (hv : v ∈ MvPolynomial.zeroLocus ℂ q.asHomogeneousIdeal.toIdeal) :
    q.asHomogeneousIdeal.toIdeal ≤ linePrimeIdeal v := by
  intro p hp
  have hcomp_mem (n : ℕ) :
      MvPolynomial.homogeneousComponent n p ∈ q.asHomogeneousIdeal.toIdeal := by
    have h := q.asHomogeneousIdeal.isHomogeneous n hp
    change ((DirectSum.decompose
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) p n :
        MvPolynomial (Fin (d + 1)) ℂ)) ∈ q.asHomogeneousIdeal.toIdeal at h
    change ((MvPolynomial.decomposition.decompose' p n :
      MvPolynomial (Fin (d + 1)) ℂ)) ∈ q.asHomogeneousIdeal.toIdeal at h
    rwa [MvPolynomial.decomposition.decompose'_apply] at h
  have hcomp_line (n : ℕ) :
      lineEval v (MvPolynomial.homogeneousComponent n p) = 0 := by
    apply Polynomial.funext
    intro c
    rw [eval_lineEval]
    rw [homogeneous_eval_smul _ n
      (MvPolynomial.homogeneousComponent_isHomogeneous n p)]
    have hzero : MvPolynomial.eval v
        (MvPolynomial.homogeneousComponent n p) = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using
        (MvPolynomial.mem_zeroLocus_iff.mp hv) _ (hcomp_mem n)
    simp [hzero]
  change lineEval v p = 0
  rw [← MvPolynomial.sum_homogeneousComponent p]
  simp [hcomp_line]

theorem projectivePointToProj_surjective_on_closed_points
    (q : ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ))
    (hClosed : IsClosed ({q} : Set (ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)))) :
    ∃ x : Space d, projectivePointToProj x = q := by
  obtain ⟨v,hvne,hvzero⟩ := exists_nonzero_zero_of_relevant q
  let x : Space d := Projectivization.mk ℂ v hvne
  have hle : q ≤ projectivePointToProj x := by
    rw [← ProjectiveSpectrum.as_ideal_le_as_ideal]
    change q.asHomogeneousIdeal.toIdeal ≤
      (lineHomogeneousPrime x.rep).toIdeal
    rw [lineHomogeneousPrime_toIdeal x.rep x.rep_nonzero]
    have hrep : linePrimeIdeal x.rep = linePrimeIdeal v := by
      obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hvne
      rw [← hc]
      exact ComplexProjectiveLineProjInvariant.linePrimeIdeal_smul v c c.ne_zero
    rw [hrep]
    exact homogeneousPrime_le_linePrimeIdeal q v hvzero
  have hmem := (ProjectiveSpectrum.le_iff_mem_closure
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) q
    (projectivePointToProj x)).mp hle
  rw [hClosed.closure_eq] at hmem
  exact ⟨x, Set.mem_singleton_iff.mp hmem⟩

end
end QuaternionicSymmetry.ComplexProjectiveProjClosedSurjection
