import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularQuotientFamily
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The literal Laurent-parameter diagonal family preserves ordinary
homogeneous degree in the projective coordinate variables. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamilyGraded

open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalRegularFamily
noncomputable section

variable {r d : ℕ}

theorem familySubstitution_isHomogeneous
    (μ : Fin (d + 1) → Fin r → ℤ)
    {p : MvPolynomial (Fin (d + 1)) ℂ} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    (familySubstitution μ p).IsHomogeneous n := by
  change (MvPolynomial.eval₂
    (MvPolynomial.C.comp (algebraMap ℂ (TorusCoordinateRing r)))
    (fun i => MvPolynomial.C (laurentMonomial (μ i)) *
      MvPolynomial.X i) p).IsHomogeneous n
  simpa only [one_mul] using hp.eval₂
    (MvPolynomial.C.comp (algebraMap ℂ (TorusCoordinateRing r)))
    (fun i => MvPolynomial.C (laurentMonomial (μ i)) *
      MvPolynomial.X i)
    (fun c => MvPolynomial.isHomogeneous_C _ _)
    (fun i => (MvPolynomial.isHomogeneous_X (TorusCoordinateRing r) i).C_mul _)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamilyGraded
