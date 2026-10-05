import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamilySpecialization

/-! The algebraic Laurent-family quotient is separated by all of its
complex-torus fibers because the extended cone ideal was identified with
the joint point-vanishing ideal. This is the faithful-fibers tool for
coaction laws. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyFiberSeparation

open ComplexProjectiveTopology ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalFamilyZeroIdeal
open ComplexProjectiveDiagonalFamilyIdealDescent
open ComplexProjectiveDiagonalRegularFamilySpecialization
open TorusLaurentRepresentation
noncomputable section

variable {r d : ℕ}

theorem specializeQuotient_jointly_zero (A : Set (Space d))
    (q :
      MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
        extendedConeIdeal (r := r) A)
    (hzero : ∀ z : ComplexTorus r,
      specializeQuotient A z q = 0) : q = 0 := by
  induction q using Quotient.inductionOn' with
  | _ p =>
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← familyZeroIdeal_eq_extendedConeIdeal A,
      mem_familyZeroIdeal_iff]
    intro z v hv
    have hz := hzero z
    change Ideal.Quotient.mk (vanishingIdeal A)
      (MvPolynomial.map (evalTorus z) p) = 0 at hz
    have hmem : MvPolynomial.map (evalTorus z) p ∈ vanishingIdeal A :=
      Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [MvPolynomial.eval₂_eq_eval_map]
    exact (mem_vanishingIdeal_iff A _).mp hmem v hv

theorem specializeQuotient_jointly_injective (A : Set (Space d)) :
    Function.Injective (fun q :
      MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) ⧸
        extendedConeIdeal (r := r) A =>
      fun z : ComplexTorus r => specializeQuotient A z q) := by
  intro q₁ q₂ h
  apply sub_eq_zero.mp
  apply specializeQuotient_jointly_zero A
  intro z
  simpa using sub_eq_zero.mpr (congrFun h z)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyFiberSeparation
