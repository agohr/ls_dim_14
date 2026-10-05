import QuaternionicSymmetry.ComplexProjectiveProjClosedSurjection

/-! The constructed classical complex projective points are closed in
Mathlib Proj. Together with closed-point surjectivity, this identifies
precisely the closed-point sets, not the full schemes or analytic topology. -/

namespace QuaternionicSymmetry.ComplexProjectiveProjClassicalClosed

open ComplexProjectiveTopology
open ComplexProjectiveLineProjPoint ComplexProjectiveLineProjLocus
open ComplexProjectiveLineProjInjective
open ComplexProjectiveProjClosedPoints ComplexProjectiveProjClosedSurjection
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

theorem projectivePointToProj_isClosed (x : Space d) :
    IsClosed ({projectivePointToProj x} : Set (ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ))) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ
  have hset : ProjectiveSpectrum.zeroLocus 𝒜
      ((projectivePointToProj x).asHomogeneousIdeal :
        Set (MvPolynomial (Fin (d + 1)) ℂ)) = {projectivePointToProj x} := by
    ext q
    constructor
    · intro hq
      have hle : projectivePointToProj x ≤ q := by
        change (projectivePointToProj x).asHomogeneousIdeal ≤ q.asHomogeneousIdeal
        exact hq
      obtain ⟨w,hwne,hwzero⟩ := exists_nonzero_zero_of_relevant q
      have hj : ∃ j : Fin (d + 1), x.rep j ≠ 0 := by
        by_contra hno
        push_neg at hno
        apply x.rep_nonzero
        funext i
        exact hno i
      obtain ⟨j,hj⟩ := hj
      have heq (i : Fin (d + 1)) :
          x.rep j * w i = x.rep i * w j := by
        have hmem : lineEquation x.rep i j ∈ q.asHomogeneousIdeal.toIdeal :=
          hq (lineEquation_mem_lineHomogeneousPrime x.rep i j)
        have h := (MvPolynomial.mem_zeroLocus_iff.mp hwzero) _ hmem
        rw [MvPolynomial.aeval_eq_eval, lineEquation_eval] at h
        exact sub_eq_zero.mp h
      have hscale : w = (w j / x.rep j) • x.rep := by
        funext i
        change w i = w j / x.rep j * x.rep i
        have h := heq i
        field_simp [hj]
        linear_combination h
      have hpoint : Projectivization.mk ℂ w hwne = x := by
        calc
          Projectivization.mk ℂ w hwne =
              Projectivization.mk ℂ x.rep x.rep_nonzero :=
            (Projectivization.mk_eq_mk_iff' ℂ _ _ hwne x.rep_nonzero).mpr
              ⟨w j / x.rep j, hscale.symm⟩
          _ = x := x.mk_rep
      have hle' : q ≤ projectivePointToProj (Projectivization.mk ℂ w hwne) := by
        rw [← ProjectiveSpectrum.as_ideal_le_as_ideal]
        change q.asHomogeneousIdeal.toIdeal ≤
          (lineHomogeneousPrime (Projectivization.mk ℂ w hwne).rep).toIdeal
        rw [ComplexProjectiveLineKernelHomogeneous.lineHomogeneousPrime_toIdeal
          (Projectivization.mk ℂ w hwne).rep
          (Projectivization.mk ℂ w hwne).rep_nonzero]
        have hrep : linePrimeIdeal (Projectivization.mk ℂ w hwne).rep =
            linePrimeIdeal w := by
          obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ w hwne
          rw [← hc]
          exact ComplexProjectiveLineProjInvariant.linePrimeIdeal_smul w c c.ne_zero
        rw [hrep]
        exact homogeneousPrime_le_linePrimeIdeal q w hwzero
      rw [hpoint] at hle'
      exact Set.mem_singleton_iff.mpr (le_antisymm hle' hle)
    · intro hq
      have hEq := Set.mem_singleton_iff.mp hq
      subst q
      exact fun _ hp => hp
  rw [← hset]
  exact ProjectiveSpectrum.isClosed_zeroLocus 𝒜 _

end
end QuaternionicSymmetry.ComplexProjectiveProjClassicalClosed
