import QuaternionicSymmetry.ComplexProjectiveConeHomogeneousIdealInput
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-! A nonzero complex coordinate line gives a genuine relevant homogeneous
prime of the standard polynomial graded ring. This is a map from actual
analytic projective points to Mathlib Proj points, not yet an equivalence. -/

namespace QuaternionicSymmetry.ComplexProjectiveLineProjPoint

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalVanishingIdeal
open scoped LinearAlgebra.Projectivization Polynomial
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

def lineEval (v : Coord d) :
    MvPolynomial (Fin (d + 1)) ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X)

def linePrimeIdeal (v : Coord d) :
    Ideal (MvPolynomial (Fin (d + 1)) ℂ) :=
  RingHom.ker (lineEval v).toRingHom

def lineHomogeneousPrime (v : Coord d) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  (linePrimeIdeal v).homogeneousCore _

theorem lineHomogeneousPrime_isPrime (v : Coord d) :
    (lineHomogeneousPrime v).toIdeal.IsPrime :=
  (RingHom.ker_isPrime (lineEval v).toRingHom).homogeneousCore

theorem lineHomogeneousPrime_relevant (v : Coord d) (hv : v ≠ 0) :
    ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) ≤
        lineHomogeneousPrime v := by
  intro h
  have hi : ∃ i : Fin (d + 1), v i ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply hv
    funext i
    exact hno i
  obtain ⟨i,hi⟩ := hi
  have hX : MvPolynomial.X i ∈ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
    HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)
      (show 0 < (1 : ℕ) by norm_num)
      (MvPolynomial.isHomogeneous_X ℂ i)
  have hker : MvPolynomial.X i ∈ linePrimeIdeal v :=
    (Ideal.toIdeal_homogeneousCore_le
      (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)
      (I := linePrimeIdeal v)) (h hX)
  have heval : lineEval v (MvPolynomial.X i) = 0 :=
    (RingHom.mem_ker).mp hker
  simp [lineEval, hi] at heval

def projectivePointToProj (x : Space d) :
    ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) where
  asHomogeneousIdeal := lineHomogeneousPrime x.rep
  isPrime := lineHomogeneousPrime_isPrime x.rep
  not_irrelevant_le := lineHomogeneousPrime_relevant x.rep x.rep_nonzero

end
end QuaternionicSymmetry.ComplexProjectiveLineProjPoint
