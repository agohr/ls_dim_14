import QuaternionicSymmetry.CompactTorusFiniteLaurentDensity

/-! Algebraic expansion of a polynomial evaluated on diagonal complex-torus
orbits.  Each ordinary monomial becomes one genuine integral character. -/

namespace QuaternionicSymmetry.CompactTorusPolynomialOrbitLaurent

open ManifoldQuaternionicTorusAction TorusLaurentRepresentation
open CompactTorusFiniteLaurentDensity MvPolynomial
open scoped BigOperators
noncomputable section

theorem character_add {r : ℕ} (μ ν : Fin r → ℤ) (z : ComplexTorus r) :
    complexWeightCharacter (μ + ν) z =
      complexWeightCharacter μ z * complexWeightCharacter ν z := by
  change (∏ i : Fin r, z i ^ (μ i + ν i)) =
    (∏ i : Fin r, z i ^ μ i) * (∏ i : Fin r, z i ^ ν i)
  simp_rw [zpow_add]
  exact Finset.prod_mul_distrib

theorem character_nat_smul {r : ℕ} (m : ℕ) (μ : Fin r → ℤ)
    (z : ComplexTorus r) :
    complexWeightCharacter (m • μ) z =
      complexWeightCharacter μ z ^ m := by
  change (∏ i : Fin r, z i ^ (m • μ) i) =
    (∏ i : Fin r, z i ^ μ i) ^ m
  simp_rw [Pi.smul_apply, Int.nsmul_eq_mul]
  have hpow (i : Fin r) : z i ^ ((m : ℤ) * μ i) = (z i ^ μ i) ^ m := by
    rw [zpow_mul' (z i) (m : ℤ) (μ i)]
    simp
  simp_rw [hpow]
  exact
    (Finset.prod_pow (s := Finset.univ) (n := m)
      (f := fun i : Fin r => z i ^ μ i))

variable {r : ℕ} {σ : Type*} [Fintype σ]

/-- Integral weight of one ordinary polynomial monomial under diagonal
coordinate weights. -/
def monomialWeight (m : σ →₀ ℕ) (μ : σ → Fin r → ℤ) : Fin r → ℤ :=
  fun i => ∑ a : σ, (m a : ℤ) * μ a i

theorem character_monomialWeight (m : σ →₀ ℕ)
    (μ : σ → Fin r → ℤ) (z : ComplexTorus r) :
    complexWeightCharacter (monomialWeight m μ) z =
      ∏ a : σ, complexWeightCharacter (μ a) z ^ m a := by
  classical
  have h (s : Finset σ) :
      complexWeightCharacter
          (fun i => ∑ a ∈ s, (m a : ℤ) * μ a i) z =
        ∏ a ∈ s, complexWeightCharacter (μ a) z ^ m a := by
    induction s using Finset.induction_on with
    | empty => simp [complexWeightCharacter]
    | @insert a s ha ih =>
      have hw : (fun i => ∑ b ∈ insert a s, (m b : ℤ) * μ b i) =
          (m a • μ a) + (fun i => ∑ b ∈ s, (m b : ℤ) * μ b i) := by
        funext i
        simp [ha, Pi.smul_apply, Int.nsmul_eq_mul]
      rw [hw, character_add, character_nat_smul, ih]
      simp [ha]
  simpa [monomialWeight] using h Finset.univ

/-- Evaluation of a polynomial along a diagonal integral-character orbit
is the explicitly indexed finite Laurent sum over its actual support. -/
theorem eval_diagonal_eq_laurent_sum
    (p : MvPolynomial σ ℂ) (μ : σ → Fin r → ℤ)
    (v : σ → ℂ) (z : ComplexTorus r) :
    eval (fun a => (complexWeightCharacter (μ a) z : ℂ) * v a) p =
      ∑ m ∈ p.support,
        (p.coeff m * ∏ a : σ, v a ^ m a) *
          (complexWeightCharacter (monomialWeight m μ) z : ℂ) := by
  classical
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro m hm
  have hchar := congrArg (fun u : ℂˣ => (u : ℂ))
    (character_monomialWeight m μ z)
  have hchar' : (complexWeightCharacter (monomialWeight m μ) z : ℂ) =
      ∏ a : σ, (complexWeightCharacter (μ a) z : ℂ) ^ m a := by
    simpa using hchar
  rw [hchar']
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  ring

/-- Preservation-ready density theorem: any ordinary polynomial equation
holding along the compact diagonal orbit of a vector holds along its full
complex-torus diagonal orbit with the same integral weights. -/
theorem eval_diagonal_zero_of_compact
    (p : MvPolynomial σ ℂ) (μ : σ → Fin r → ℤ)
    (v : σ → ℂ)
    (h : ∀ t : Torus r,
      eval (fun a =>
        (complexWeightCharacter (μ a) (compactInclusion r t) : ℂ) * v a) p = 0) :
    ∀ z : ComplexTorus r,
      eval (fun a => (complexWeightCharacter (μ a) z : ℂ) * v a) p = 0 := by
  classical
  have hLaurent : ∀ t : Torus r,
      ∑ m ∈ p.support,
        (p.coeff m * ∏ a : σ, v a ^ m a) *
          (complexWeightCharacter (monomialWeight m μ)
            (compactInclusion r t) : ℂ) = 0 := by
    intro t
    rw [← eval_diagonal_eq_laurent_sum]
    exact h t
  intro z
  rw [eval_diagonal_eq_laurent_sum]
  exact finite_laurent_vanish_of_compact p.support
    (fun m => p.coeff m * ∏ a : σ, v a ^ m a)
    (fun m => monomialWeight m μ) hLaurent z

end
end QuaternionicSymmetry.CompactTorusPolynomialOrbitLaurent
