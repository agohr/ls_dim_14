import QuaternionicSymmetry.ComplexProjectiveLineProjInjective
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.GradedAlgebra.Radical

/-! For a nonzero vector, the kernel of evaluation along its complex line
is itself a homogeneous prime ideal. Its homogeneous core is therefore
exactly the kernel, not merely a prime subideal. -/

namespace QuaternionicSymmetry.ComplexProjectiveLineKernelHomogeneous

open ComplexProjectiveTopology
open ComplexProjectiveLineProjPoint ComplexProjectiveLineProjLocus
open ComplexProjectiveLineProjInjective
open scoped Polynomial
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

def lineEquationIdeal (v : Coord d) (j : Fin (d + 1)) :
    Ideal (MvPolynomial (Fin (d + 1)) ℂ) :=
  Ideal.span (Set.range (fun i => lineEquation v i j))

theorem lineEquationIdeal_isHomogeneous (v : Coord d) (j : Fin (d + 1)) :
    (lineEquationIdeal v j).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) := by
  apply Ideal.homogeneous_span
  rintro p ⟨i,rfl⟩
  exact ⟨1, lineEquation_isHomogeneous v i j⟩

theorem mem_lineEquationIdeal_zeroLocus_iff
    (v : Coord d) (j : Fin (d + 1)) (hj : v j ≠ 0)
    (w : Coord d) :
    w ∈ MvPolynomial.zeroLocus ℂ (lineEquationIdeal v j) ↔
      ∃ c : ℂ, w = c • v := by
  change w ∈ MvPolynomial.zeroLocus ℂ
    (Ideal.span (Set.range (fun i => lineEquation v i j))) ↔ _
  rw [MvPolynomial.zeroLocus_span]
  constructor
  · intro hw
    have heq (i : Fin (d + 1)) :
        v j * w i = v i * w j := by
      have h := hw (lineEquation v i j) ⟨i,rfl⟩
      rw [MvPolynomial.aeval_eq_eval, lineEquation_eval] at h
      exact sub_eq_zero.mp h
    refine ⟨w j / v j, ?_⟩
    funext i
    change w i = w j / v j * v i
    have h := heq i
    field_simp [hj]
    linear_combination h
  · rintro ⟨c,rfl⟩ p ⟨i,rfl⟩
    rw [MvPolynomial.aeval_eq_eval, lineEquation_eval]
    simp [Pi.smul_apply, smul_eq_mul]
    ring

theorem linePrimeIdeal_eq_radical_lineEquationIdeal
    (v : Coord d) (j : Fin (d + 1)) (hj : v j ≠ 0) :
    linePrimeIdeal v = (lineEquationIdeal v j).radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  ext p
  simp only [linePrimeIdeal, RingHom.mem_ker,
    MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro hp w hw
    obtain ⟨c,rfl⟩ := (mem_lineEquationIdeal_zeroLocus_iff v j hj w).mp hw
    have h := congrArg (Polynomial.eval c) hp
    simpa [eval_lineEval, MvPolynomial.aeval_eq_eval] using h
  · intro hp
    apply Polynomial.funext
    intro c
    have h := hp (c • v)
      ((mem_lineEquationIdeal_zeroLocus_iff v j hj _).mpr ⟨c,rfl⟩)
    simpa [eval_lineEval, MvPolynomial.aeval_eq_eval] using h

theorem linePrimeIdeal_isHomogeneous (v : Coord d) (hv : v ≠ 0) :
    (linePrimeIdeal v).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) := by
  have hj : ∃ j : Fin (d + 1), v j ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply hv
    funext i
    exact hno i
  obtain ⟨j,hj⟩ := hj
  rw [linePrimeIdeal_eq_radical_lineEquationIdeal v j hj]
  exact (lineEquationIdeal_isHomogeneous v j).radical

theorem lineHomogeneousPrime_toIdeal (v : Coord d) (hv : v ≠ 0) :
    (lineHomogeneousPrime v).toIdeal = linePrimeIdeal v :=
  (linePrimeIdeal_isHomogeneous v hv).toIdeal_homogeneousCore_eq_self

end
end QuaternionicSymmetry.ComplexProjectiveLineKernelHomogeneous
