import QuaternionicSymmetry.ComplexProjectiveActualConeProjCoordinateCover
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartVanishingIdeal

/-! Literal dehomogenization of actual cone equations in a standard
projective coordinate chart. It descends to a ring map from the actual
homogeneous cone quotient to the actual affine-chart quotient and sends
the chosen coordinate class to one. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDehomogenization

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveActualConeProjCoordinates
noncomputable section

variable {d : ℕ}

def dehomogenize (i : Fin (d + 1)) :
    MvPolynomial (Fin (d + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ :=
  MvPolynomial.aeval
    (Fin.insertNth (α := fun _ : Fin (d + 1) => MvPolynomial (Fin d) ℂ)
      i 1 (fun k => MvPolynomial.X k))

theorem dehomogenize_coordinate (i j : Fin (d + 1)) :
    dehomogenize i (MvPolynomial.X j) =
      Fin.insertNth (α := fun _ : Fin (d + 1) => MvPolynomial (Fin d) ℂ) i 1
        (fun k => MvPolynomial.X k) j := by
  simp [dehomogenize]

theorem dehomogenize_chosen_coordinate (i : Fin (d + 1)) :
    dehomogenize i (MvPolynomial.X i) = 1 := by
  simp [dehomogenize_coordinate]

theorem eval_dehomogenize (i : Fin (d + 1))
    (w : Fin d → ℂ) (p : MvPolynomial (Fin (d + 1)) ℂ) :
    MvPolynomial.eval w (dehomogenize i p) =
      MvPolynomial.eval (homogeneousVector d i w) p := by
  have h : (MvPolynomial.aeval w).comp (dehomogenize i) =
      MvPolynomial.aeval (homogeneousVector d i w) := by
    ext j
    refine Fin.succAboveCases i ?_ ?_ j
    · simp [dehomogenize_coordinate, homogeneousVector]
    · intro k
      simp [dehomogenize_coordinate, homogeneousVector]
  exact congrArg (fun f : _ →ₐ[ℂ] ℂ => f p) h

theorem dehomogenize_mem_chartVanishingIdeal
    (A : Set (Space d)) (i : Fin (d + 1))
    {p : MvPolynomial (Fin (d + 1)) ℂ}
    (hp : p ∈ vanishingIdeal A) :
    dehomogenize i p ∈ chartVanishingIdeal A i := by
  rw [mem_chartVanishingIdeal_iff]
  intro w hw
  rw [eval_dehomogenize]
  apply (mem_vanishingIdeal_iff A p).mp hp
  right
  refine ⟨homogeneousVector_ne_zero d i w, ?_⟩
  change euclideanPoint d i w ∈ A
  simpa only [projectiveChart_symm_apply] using hw

def quotientDehomogenize (A : Set (Space d)) (i : Fin (d + 1)) :
    (MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) →+*
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) :=
  Ideal.Quotient.lift (vanishingIdeal A)
    ((Ideal.Quotient.mk (chartVanishingIdeal A i)).comp
      (dehomogenize i).toRingHom)
    (by
      intro p hp
      change (Ideal.Quotient.mk (chartVanishingIdeal A i))
        (dehomogenize i p) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (dehomogenize_mem_chartVanishingIdeal A i hp))

theorem quotientDehomogenize_chosen_coordinate
    (A : Set (Space d)) (i : Fin (d + 1)) :
    quotientDehomogenize A i (coordinateClass A i) = 1 := by
  simp [quotientDehomogenize, coordinateClass,
    dehomogenize_chosen_coordinate]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDehomogenization
