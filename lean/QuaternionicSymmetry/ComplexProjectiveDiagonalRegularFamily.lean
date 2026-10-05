import QuaternionicSymmetry.ComplexProjectiveDiagonalAlgebraicCharts
import QuaternionicSymmetry.ComplexProjectiveDiagonalVanishingIdeal

/-! A literal regular family of diagonal substitutions on the ambient
homogeneous coordinate polynomial algebra. The parameter ring is the
Laurent coordinate ring of the algebraic complex torus. Descending this
family through the actual cone ideal is a separate step. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamily

open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open TorusLaurentRepresentation
noncomputable section

variable {r d : ℕ}

def familySubstitution (μ : Fin (d + 1) → Fin r → ℤ) :
    MvPolynomial (Fin (d + 1)) ℂ →+*
      MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r) :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (algebraMap ℂ (TorusCoordinateRing r)))
    (fun i => MvPolynomial.C (laurentMonomial (μ i)) * MvPolynomial.X i)

@[simp] theorem familySubstitution_X
    (μ : Fin (d + 1) → Fin r → ℤ) (i : Fin (d + 1)) :
    familySubstitution μ (MvPolynomial.X i) =
      MvPolynomial.C (laurentMonomial (μ i)) * MvPolynomial.X i := by
  simp [familySubstitution]

/-- Every complex torus point specializes the regular family to the
previously constructed exact diagonal coordinate automorphism. -/
theorem specialize_familySubstitution
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) :
    (MvPolynomial.map (evalTorus z)).comp (familySubstitution μ) =
      diagonalSubstitution μ z := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [familySubstitution, diagonalSubstitution, evalTorus]
  · intro i
    simp [familySubstitution, diagonalSubstitution,
      evalTorus_laurentMonomial]

theorem eval₂_familySubstitution
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (v : Fin (d + 1) → ℂ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) :
    MvPolynomial.eval₂ (evalTorus z) v (familySubstitution μ p) =
      MvPolynomial.eval
        (ComplexProjectiveDiagonalAction.diagonalEquiv μ z v) p := by
  rw [MvPolynomial.eval₂_eq_eval_map]
  change MvPolynomial.eval v
      ((MvPolynomial.map (evalTorus z)).comp (familySubstitution μ) p) = _
  rw [specialize_familySubstitution]
  exact eval_diagonalSubstitution μ z v p

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamily
