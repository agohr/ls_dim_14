import QuaternionicSymmetry.ComplexProjectiveLineKernelHomogeneous

/-! The analytic complex points of a nonempty homogeneous projective
cutout satisfy exactly the same homogeneous equations as their genuine
Proj points. This is a set-theoretic comparison on the constructed image,
not a surjectivity, topology, scheme-smoothness or contact comparison. -/

namespace QuaternionicSymmetry.ComplexProjectiveProjCutoutComparison

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveAffineConeHomogeneousIdeal
open ComplexProjectiveLineProjPoint ComplexProjectiveLineProjLocus
open ComplexProjectiveLineKernelHomogeneous
open scoped LinearAlgebra.Projectivization Polynomial
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

theorem equation_mem_vanishingIdeal {N : ℕ}
    (P : Fin N → Equation d) (hNonempty : (zeroLocus P).Nonempty)
    (j : Fin N) :
    (P j).polynomial ∈ vanishingIdeal (zeroLocus P) := by
  rw [mem_vanishingIdeal_iff]
  intro v hv
  have hv' : v ∈ MvPolynomial.zeroLocus ℂ (equationIdeal P) :=
    (affineCone_eq_zeroLocus P hNonempty) ▸ hv
  have hmem : (P j).polynomial ∈ equationIdeal P :=
    Ideal.subset_span ⟨j,rfl⟩
  simpa only [MvPolynomial.aeval_eq_eval] using
    (MvPolynomial.mem_zeroLocus_iff.mp hv') _ hmem

theorem mem_cutout_iff_mem_proj_zeroLocus
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (x : Space d) :
    x ∈ A ↔
      projectivePointToProj x ∈
        ProjectiveSpectrum.zeroLocus
          (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)
          (vanishingIdeal A : Set (MvPolynomial (Fin (d + 1)) ℂ)) := by
  constructor
  · exact projectivePointToProj_mem_zeroLocus A hA x
  · intro hx
    obtain ⟨N,P,hAP⟩ := hA
    have hPj (j : Fin N) : (P j).polynomial ∈ vanishingIdeal A := by
      rw [hAP]
      exact equation_mem_vanishingIdeal P (hAP ▸ hNonempty) j
    have hEval (j : Fin N) :
        MvPolynomial.eval x.rep (P j).polynomial = 0 := by
      have hmem : (P j).polynomial ∈ lineHomogeneousPrime x.rep := hx (hPj j)
      change (P j).polynomial ∈ (lineHomogeneousPrime x.rep).toIdeal at hmem
      rw [lineHomogeneousPrime_toIdeal x.rep x.rep_nonzero] at hmem
      have h := (RingHom.mem_ker).mp hmem
      have h' := congrArg (Polynomial.eval 1) h
      simpa [eval_lineEval] using h'
    have hmk : Projectivization.mk ℂ x.rep x.rep_nonzero ∈ zeroLocus P :=
      (mem_zeroLocus_mk_iff P x.rep x.rep_nonzero).mpr hEval
    rw [← hAP, x.mk_rep] at hmk
    exact hmk

end
end QuaternionicSymmetry.ComplexProjectiveProjCutoutComparison
