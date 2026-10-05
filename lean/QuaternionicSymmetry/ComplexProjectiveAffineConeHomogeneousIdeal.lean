import QuaternionicSymmetry.ComplexProjectiveDiagonalQuotientAlgAction
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.GradedAlgebra.Radical

/-! The affine cone of a nonempty projective homogeneous cutout has a
homogeneous radical vanishing ideal. Nonemptiness handles possible
degree-zero equations without silently assuming positive degrees. -/

namespace QuaternionicSymmetry.ComplexProjectiveAffineConeHomogeneousIdeal

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

def equationIdeal {N : ℕ} (P : Fin N → Equation d) :
    Ideal (MvPolynomial (Fin (d + 1)) ℂ) :=
  Ideal.span (Set.range (fun j => (P j).polynomial))

theorem equationIdeal_isHomogeneous {N : ℕ} (P : Fin N → Equation d) :
    (equationIdeal P).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) := by
  apply Ideal.homogeneous_span
  rintro p ⟨j, rfl⟩
  exact ⟨(P j).degree, (P j).homogeneous⟩

theorem affineCone_eq_zeroLocus {N : ℕ} (P : Fin N → Equation d)
    (hNonempty : (zeroLocus P).Nonempty) :
    affineCone (zeroLocus P) = MvPolynomial.zeroLocus ℂ (equationIdeal P) := by
  ext v
  change v ∈ affineCone (zeroLocus P) ↔
    v ∈ MvPolynomial.zeroLocus ℂ
      (Ideal.span (Set.range (fun j => (P j).polynomial)))
  rw [MvPolynomial.zeroLocus_span]
  change (v = 0 ∨ ∃ hv : v ≠ 0, Projectivization.mk ℂ v hv ∈ zeroLocus P) ↔
    ∀ p ∈ Set.range (fun j => (P j).polynomial), MvPolynomial.aeval v p = 0
  constructor
  · rintro (rfl | ⟨hv,hvA⟩)
    · intro p hp
      obtain ⟨j,hjp⟩ := hp
      subst p
      obtain ⟨x,hx⟩ := hNonempty
      induction x using Projectivization.ind with
      | h w hw =>
        have hj : MvPolynomial.eval w (P j).polynomial = 0 :=
          (mem_zeroLocus_mk_iff P w hw).mp hx j
        have hzero := homogeneous_eval_smul (P j).polynomial
          (P j).degree (P j).homogeneous (0 : ℂ) w
        simpa [MvPolynomial.aeval_eq_eval, hj] using hzero
    · intro p hp
      obtain ⟨j,hjp⟩ := hp
      subst p
      simpa only [MvPolynomial.aeval_eq_eval] using
        (mem_zeroLocus_mk_iff P v hv).mp hvA j
  · intro hv
    by_cases hne : v = 0
    · exact Or.inl hne
    · refine Or.inr ⟨hne, (mem_zeroLocus_mk_iff P v hne).mpr ?_⟩
      intro j
      simpa only [MvPolynomial.aeval_eq_eval] using
        hv _ ⟨j,rfl⟩

theorem vanishingIdeal_isHomogeneous (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    (vanishingIdeal A).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) := by
  obtain ⟨N,P,rfl⟩ := hA
  have hCone := affineCone_eq_zeroLocus P hNonempty
  have hEq : vanishingIdeal (zeroLocus P) = (equationIdeal P).radical := by
    ext p
    rw [mem_vanishingIdeal_iff]
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)
      (equationIdeal P)]
    simp only [MvPolynomial.mem_vanishingIdeal_iff]
    simpa only [hCone, MvPolynomial.aeval_eq_eval]
  rw [hEq]
  exact (equationIdeal_isHomogeneous P).radical

end
end QuaternionicSymmetry.ComplexProjectiveAffineConeHomogeneousIdeal
