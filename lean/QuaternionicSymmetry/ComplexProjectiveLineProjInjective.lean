import QuaternionicSymmetry.ComplexProjectiveLineProjInvariant

/-! Linear homogeneous equations distinguish complex projective lines
inside Mathlib's relevant homogeneous-prime Proj points. -/

namespace QuaternionicSymmetry.ComplexProjectiveLineProjInjective

open ComplexProjectiveTopology
open ComplexProjectiveLineProjPoint
open scoped LinearAlgebra.Projectivization Polynomial
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

def lineEquation (v : Coord d) (i j : Fin (d + 1)) :
    MvPolynomial (Fin (d + 1)) ℂ :=
  MvPolynomial.C (v j) * MvPolynomial.X i -
    MvPolynomial.C (v i) * MvPolynomial.X j

theorem lineEquation_isHomogeneous (v : Coord d) (i j : Fin (d + 1)) :
    (lineEquation v i j).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_X ℂ i).C_mul _).sub
    ((MvPolynomial.isHomogeneous_X ℂ j).C_mul _)

theorem lineEquation_mem_lineHomogeneousPrime
    (v : Coord d) (i j : Fin (d + 1)) :
    lineEquation v i j ∈ lineHomogeneousPrime v := by
  apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)
    ⟨1, lineEquation_isHomogeneous v i j⟩
  change lineEval v (lineEquation v i j) = 0
  simp [lineEval, lineEquation]
  ring

theorem lineEquation_eval (v w : Coord d) (i j : Fin (d + 1)) :
    MvPolynomial.eval w (lineEquation v i j) =
      v j * w i - v i * w j := by
  simp [lineEquation]

theorem projectivePointToProj_injective :
    Function.Injective (projectivePointToProj (d := d)) := by
  intro x y hxy
  have hcore : lineHomogeneousPrime x.rep = lineHomogeneousPrime y.rep :=
    congrArg ProjectiveSpectrum.asHomogeneousIdeal hxy
  have hj : ∃ j : Fin (d + 1), y.rep j ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply y.rep_nonzero
    funext i
    exact hno i
  obtain ⟨j,hj⟩ := hj
  have hlin (i : Fin (d + 1)) :
      y.rep j * x.rep i = y.rep i * x.rep j := by
    have hmem : lineEquation y.rep i j ∈ lineHomogeneousPrime x.rep := by
      rw [hcore]
      exact lineEquation_mem_lineHomogeneousPrime y.rep i j
    have hker : lineEquation y.rep i j ∈ linePrimeIdeal x.rep :=
      (Ideal.toIdeal_homogeneousCore_le
        (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)
        (I := linePrimeIdeal x.rep)) hmem
    have heval : MvPolynomial.eval x.rep (lineEquation y.rep i j) = 0 := by
      have h := (RingHom.mem_ker).mp hker
      have h' := congrArg (Polynomial.eval 1) h
      simpa [ComplexProjectiveLineProjLocus.eval_lineEval] using h'
    rw [lineEquation_eval] at heval
    exact sub_eq_zero.mp heval
  have hscale : (x.rep j / y.rep j) • y.rep = x.rep := by
    funext i
    change x.rep j / y.rep j * y.rep i = x.rep i
    have h := hlin i
    field_simp [hj]
    linear_combination -h
  calc
    x = Projectivization.mk ℂ x.rep x.rep_nonzero := x.mk_rep.symm
    _ = Projectivization.mk ℂ y.rep y.rep_nonzero :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ x.rep_nonzero y.rep_nonzero).mpr
        ⟨x.rep j / y.rep j, hscale⟩
    _ = y := y.mk_rep

end
end QuaternionicSymmetry.ComplexProjectiveLineProjInjective
