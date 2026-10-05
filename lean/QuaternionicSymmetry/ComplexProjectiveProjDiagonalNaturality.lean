import QuaternionicSymmetry.ComplexProjectiveProjContinuous
import QuaternionicSymmetry.ComplexProjectiveDiagonalGradedRingAction

/-! The actual diagonal action on projective points agrees with the
contravariant polynomial substitution on their Proj prime ideals. This
checks the direction of the algebraic action without postulating a scheme
or analytification comparison. -/

namespace QuaternionicSymmetry.ComplexProjectiveProjDiagonalNaturality

open ComplexProjectiveTopology ComplexProjectiveLineProjPoint
open ComplexProjectiveLineProjInvariant ComplexProjectiveLineKernelHomogeneous
open ComplexProjectiveProjContinuous ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalVanishingIdeal TorusLaurentRepresentation
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {r d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

theorem linePrimeIdeal_diagonal
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) (v : Coord d) :
    linePrimeIdeal (diagonalEquiv μ z v) =
      Ideal.comap (diagonalSubstitution μ z) (linePrimeIdeal v) := by
  ext p
  change p ∈ linePrimeIdeal (diagonalEquiv μ z v) ↔
    diagonalSubstitution μ z p ∈ linePrimeIdeal v
  simp only [mem_linePrimeIdeal_iff, eval_diagonalSubstitution,
    map_smul]

theorem projectivePointToProj_action_ideal
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) (x : Space d) :
    (projectivePointToProj (projectiveAction μ z x)).asHomogeneousIdeal.toIdeal =
      Ideal.comap (diagonalSubstitution μ z)
        (projectivePointToProj x).asHomogeneousIdeal.toIdeal := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [projectiveAction_mk, projectivePointToProj_mk,
      projectivePointToProj_mk]
    change (lineHomogeneousPrime (diagonalEquiv μ z v)).toIdeal =
      Ideal.comap (diagonalSubstitution μ z) (lineHomogeneousPrime v).toIdeal
    rw [lineHomogeneousPrime_toIdeal _
      ((diagonalEquiv μ z).map_ne_zero_iff.mpr hv),
      lineHomogeneousPrime_toIdeal v hv]
    exact linePrimeIdeal_diagonal μ z v

theorem equivariant_projective_map_ideal {X : Type*}
    (f : X → Space d) (μ : Fin (d + 1) → Fin r → ℤ)
    (ρ : ComplexTorus r → X → X)
    (hρ : ∀ z x, f (ρ z x) = projectiveAction μ z (f x))
    (z : ComplexTorus r) (x : X) :
    (projectivePointToProj (f (ρ z x))).asHomogeneousIdeal.toIdeal =
      Ideal.comap (diagonalSubstitution μ z)
        (projectivePointToProj (f x)).asHomogeneousIdeal.toIdeal := by
  rw [hρ]
  exact projectivePointToProj_action_ideal μ z (f x)

end
end QuaternionicSymmetry.ComplexProjectiveProjDiagonalNaturality
