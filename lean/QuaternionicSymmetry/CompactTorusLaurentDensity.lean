import QuaternionicSymmetry.CompactTorusPolynomialDensity

/-! Denominator-cleared Laurent vanishing on the complex torus.  A later
orbit-coordinate calculation may supply the polynomial numerator; the
identity theorem itself is internal and does not assume algebraicity of a
projective image. -/

namespace QuaternionicSymmetry.CompactTorusLaurentDensity

open ManifoldQuaternionicTorusAction TorusLaurentRepresentation
open CompactTorusPolynomialDensity MvPolynomial
noncomputable section

/-- Polynomial vanishing on all compact-torus tuples propagates to every
complex-torus tuple. -/
theorem polynomial_vanishes_on_complex {r : ℕ}
    (p : MvPolynomial (Fin r) ℂ)
    (h : ∀ t : Torus r,
      eval (fun i => ((t i : Circle) : ℂ)) p = 0)
    (z : ComplexTorus r) :
    eval (fun i => (z i : ℂ)) p = 0 := by
  rw [polynomial_eq_zero_of_compact p h]
  simp

/-- Multiplication by one invertible Laurent monomial clears all negative
exponents. Once a polynomial numerator has been identified, compact-torus
vanishing implies complex-torus vanishing without a density axiom. -/
theorem vanishes_on_complex_of_polynomial_numerator {r : ℕ}
    (F : ComplexTorus r → ℂ) (p : MvPolynomial (Fin r) ℂ)
    (μ : Fin r → ℤ)
    (hNumerator : ∀ z : ComplexTorus r,
      F z * (complexWeightCharacter μ z : ℂ) =
        eval (fun i => (z i : ℂ)) p)
    (hCompact : ∀ t : Torus r, F (compactInclusion r t) = 0) :
    ∀ z : ComplexTorus r, F z = 0 := by
  have hp : ∀ t : Torus r,
      eval (fun i => ((t i : Circle) : ℂ)) p = 0 := by
    intro t
    have ht := hNumerator (compactInclusion r t)
    rw [hCompact] at ht
    simpa [compactInclusion] using ht.symm
  intro z
  have hz := hNumerator z
  rw [polynomial_vanishes_on_complex p hp z] at hz
  exact (mul_eq_zero.mp hz).resolve_right (complexWeightCharacter μ z).ne_zero

end
end QuaternionicSymmetry.CompactTorusLaurentDensity
