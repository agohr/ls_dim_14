import QuaternionicSymmetry.ComplexProjectiveLaurentReconstruction

/-! The joint torus-times-cone point-vanishing ideal is exactly the
extension of the actual affine-cone ideal to the Laurent parameter ring.
This is the algebraic descent condition for the regular diagonal family. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyIdealDescent

open ComplexProjectiveTopology ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalFamilyZeroIdeal
open ComplexProjectiveLaurentCoefficient
open ComplexProjectiveLaurentReconstruction
open TorusLaurentRepresentation
noncomputable section

variable {r d : ℕ}

def baseChange : MvPolynomial (Fin (d + 1)) ℂ →+*
    MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) :=
  MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r))

def extendedConeIdeal (A : Set (Space d)) :
    Ideal (MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r)) :=
  Ideal.map (baseChange (r := r)) (vanishingIdeal A)

theorem familyZeroIdeal_le_extendedConeIdeal (A : Set (Space d)) :
    familyZeroIdeal (r := r) A ≤ extendedConeIdeal (r := r) A := by
  intro p hp
  rw [reconstruct p]
  apply Ideal.sum_mem
  intro μ hμ
  exact Ideal.mul_mem_left _ _
    (Ideal.mem_map_of_mem (baseChange (r := r))
      (laurentCoefficient_mem_vanishingIdeal A p hp μ))

theorem extendedConeIdeal_le_familyZeroIdeal (A : Set (Space d)) :
    extendedConeIdeal (r := r) A ≤ familyZeroIdeal (r := r) A := by
  apply (Ideal.map_le_iff_le_comap).mpr
  intro p hp
  rw [Ideal.mem_comap, mem_familyZeroIdeal_iff]
  intro z v hv
  change MvPolynomial.eval₂ (evalTorus z) v
    (MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) = 0
  rw [MvPolynomial.eval₂_map]
  have hc : (evalTorus z).comp (algebraMap ℂ (TorusCoordinateRing r)) =
      RingHom.id ℂ := by
    ext c
    simp [evalTorus]
  rw [hc]
  simpa using (mem_vanishingIdeal_iff A p).mp hp v hv

theorem familyZeroIdeal_eq_extendedConeIdeal (A : Set (Space d)) :
    familyZeroIdeal (r := r) A = extendedConeIdeal (r := r) A :=
  le_antisymm (familyZeroIdeal_le_extendedConeIdeal A)
    (extendedConeIdeal_le_familyZeroIdeal A)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyIdealDescent
