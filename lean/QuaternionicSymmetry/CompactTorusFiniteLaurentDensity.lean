import QuaternionicSymmetry.CompactTorusLaurentDensity

/-! Explicit denominator clearing for finite sums of genuine integral torus
characters. The caller supplies a common exponent shift; no finiteness or
algebraicity of a projective image is hidden in this statement. -/

namespace QuaternionicSymmetry.CompactTorusFiniteLaurentDensity

open ManifoldQuaternionicTorusAction TorusLaurentRepresentation
open CompactTorusLaurentDensity MvPolynomial
open scoped BigOperators
noncomputable section

variable {r : ℕ} {ι : Type*} [DecidableEq ι]

def clearedPolynomial (s : Finset ι) (c : ι → ℂ)
    (μ : ι → Fin r → ℤ) (ν : Fin r → ℤ) :
    MvPolynomial (Fin r) ℂ :=
  ∑ j ∈ s, C (c j) * ∏ i : Fin r, X i ^ (μ j i + ν i).toNat

theorem eval_clearedPolynomial (s : Finset ι) (c : ι → ℂ)
    (μ : ι → Fin r → ℤ) (ν : Fin r → ℤ)
    (hν : ∀ j ∈ s, ∀ i, 0 ≤ μ j i + ν i)
    (z : ComplexTorus r) :
    eval (fun i => (z i : ℂ)) (clearedPolynomial s c μ ν) =
      (complexWeightCharacter ν z : ℂ) *
        ∑ j ∈ s, c j * (complexWeightCharacter (μ j) z : ℂ) := by
  let a : Fin r → ℂ := fun i => (z i : ℂ)
  have hcharacter (κ : Fin r → ℤ) :
      (complexWeightCharacter κ z : ℂ) = ∏ i : Fin r, a i ^ κ i := by
    simp [complexWeightCharacter, a]
  have hterm (j : ι) (hj : j ∈ s) :
      ∏ i : Fin r, a i ^ (μ j i + ν i).toNat =
        (∏ i : Fin r, a i ^ ν i) * (∏ i : Fin r, a i ^ μ j i) := by
    have hpow (i : Fin r) :
        a i ^ (μ j i + ν i).toNat = a i ^ ν i * a i ^ μ j i := by
      have hcast : (((μ j i + ν i).toNat : ℕ) : ℤ) = μ j i + ν i :=
        Int.toNat_of_nonneg (hν j hj i)
      have hai : a i ≠ 0 := (z i).ne_zero
      calc
        a i ^ (μ j i + ν i).toNat = a i ^ (((μ j i + ν i).toNat : ℕ) : ℤ) := by
          rw [zpow_natCast]
        _ = a i ^ (μ j i + ν i) := by rw [hcast]
        _ = _ := by rw [zpow_add₀ hai]; ring
    simp_rw [hpow]
    rw [Finset.prod_mul_distrib]
  simp only [clearedPolynomial, map_sum, eval_mul, eval_C,
    eval_prod, eval_pow, eval_X]
  rw [hcharacter ν]
  simp_rw [hcharacter]
  calc
    ∑ j ∈ s, c j * ∏ i : Fin r, a i ^ (μ j i + ν i).toNat =
        ∑ j ∈ s, c j *
          ((∏ i : Fin r, a i ^ ν i) * (∏ i : Fin r, a i ^ μ j i)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hterm j hj]
    _ = (∏ i : Fin r, a i ^ ν i) *
          ∑ j ∈ s, c j * (∏ i : Fin r, a i ^ μ j i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- A finite Laurent sum of genuine integral characters is determined by its
values on the compact torus, given an explicit common exponent shift. -/
theorem finite_laurent_vanish_of_compact_with_shift
    (s : Finset ι) (c : ι → ℂ) (μ : ι → Fin r → ℤ)
    (ν : Fin r → ℤ) (hν : ∀ j ∈ s, ∀ i, 0 ≤ μ j i + ν i)
    (h : ∀ t : Torus r,
      ∑ j ∈ s, c j *
        (complexWeightCharacter (μ j) (compactInclusion r t) : ℂ) = 0) :
    ∀ z : ComplexTorus r,
      ∑ j ∈ s, c j * (complexWeightCharacter (μ j) z : ℂ) = 0 := by
  apply vanishes_on_complex_of_polynomial_numerator
    (fun z => ∑ j ∈ s, c j * (complexWeightCharacter (μ j) z : ℂ))
    (clearedPolynomial s c μ ν) ν
  · intro z
    rw [eval_clearedPolynomial s c μ ν hν z]
    ring
  · exact h

/-- There is always a common shift: the finite supremum of coordinatewise
absolute weights clears every denominator. -/
theorem finite_laurent_vanish_of_compact
    (s : Finset ι) (c : ι → ℂ) (μ : ι → Fin r → ℤ)
    (h : ∀ t : Torus r,
      ∑ j ∈ s, c j *
        (complexWeightCharacter (μ j) (compactInclusion r t) : ℂ) = 0) :
    ∀ z : ComplexTorus r,
      ∑ j ∈ s, c j * (complexWeightCharacter (μ j) z : ℂ) = 0 := by
  let ν : Fin r → ℤ := fun i => (s.sup (fun j => (μ j i).natAbs) : ℕ)
  have hν : ∀ j ∈ s, ∀ i, 0 ≤ μ j i + ν i := by
    intro j hj i
    have hnat : (μ j i).natAbs ≤ s.sup (fun q => (μ q i).natAbs) :=
      Finset.le_sup (f := fun q => (μ q i).natAbs) hj
    have hcast : ((μ j i).natAbs : ℤ) ≤ ν i := by
      change ((μ j i).natAbs : ℤ) ≤
        ((s.sup (fun q => (μ q i).natAbs) : ℕ) : ℤ)
      exact_mod_cast hnat
    have hneg : -(μ j i) ≤ ((μ j i).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact neg_le_abs _
    omega
  exact finite_laurent_vanish_of_compact_with_shift s c μ ν hν h

end
end QuaternionicSymmetry.CompactTorusFiniteLaurentDensity
