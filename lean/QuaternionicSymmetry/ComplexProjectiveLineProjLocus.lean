import QuaternionicSymmetry.ComplexProjectiveLineProjPoint
import Mathlib.Algebra.Polynomial.Roots

/-! A point of an actual homogeneous projective cutout lands in the
corresponding literal closed locus of Mathlib's projective spectrum. -/

namespace QuaternionicSymmetry.ComplexProjectiveLineProjLocus

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveAffineConeHomogeneousIdeal
open ComplexProjectiveLineProjPoint
open scoped LinearAlgebra.Projectivization Polynomial
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

theorem eval_lineEval (v : Coord d)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (c : ℂ) :
    Polynomial.eval c (lineEval v p) = MvPolynomial.eval (c • v) p := by
  have h : (Polynomial.evalRingHom c).comp (lineEval v).toRingHom =
      evalAt (c • v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lineEval, evalAt]
    · intro i
      simp [lineEval, evalAt]
      exact mul_comm _ _
  exact congrArg (fun f : MvPolynomial (Fin (d + 1)) ℂ →+* ℂ => f p) h

theorem smul_rep_mem_affineCone (A : Set (Space d))
    (x : Space d) (hx : x ∈ A) (c : ℂ) :
    c • x.rep ∈ affineCone A := by
  by_cases hc : c = 0
  · left
    simp [hc]
  · right
    have hne : c • x.rep ≠ 0 := smul_ne_zero hc x.rep_nonzero
    refine ⟨hne, ?_⟩
    have heq : Projectivization.mk ℂ (c • x.rep) hne = x := by
      calc
        _ = Projectivization.mk ℂ x.rep x.rep_nonzero :=
          (Projectivization.mk_eq_mk_iff' ℂ _ _ hne x.rep_nonzero).mpr ⟨c,rfl⟩
        _ = x := x.mk_rep
    simpa only [heq] using hx

theorem vanishingIdeal_le_linePrimeIdeal
    (A : Set (Space d)) (x : Space d) (hx : x ∈ A) :
    vanishingIdeal A ≤ linePrimeIdeal x.rep := by
  intro p hp
  change lineEval x.rep p = 0
  apply Polynomial.funext
  intro c
  rw [eval_lineEval]
  simpa using (mem_vanishingIdeal_iff A p).mp hp _
    (smul_rep_mem_affineCone A x hx c)

theorem projectivePointToProj_mem_zeroLocus
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (x : Space d) (hx : x ∈ A) :
    projectivePointToProj x ∈
      ProjectiveSpectrum.zeroLocus
        (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)
        (vanishingIdeal A : Set (MvPolynomial (Fin (d + 1)) ℂ)) := by
  change vanishingIdeal A ≤
    (lineHomogeneousPrime x.rep).toIdeal
  have hHom := vanishingIdeal_isHomogeneous A hA ⟨x,hx⟩
  have hle := Ideal.homogeneousCore_mono
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)
    (vanishingIdeal_le_linePrimeIdeal A x hx)
  rw [← hHom.toIdeal_homogeneousCore_eq_self]
  exact hle

end
end QuaternionicSymmetry.ComplexProjectiveLineProjLocus
