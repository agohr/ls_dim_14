import QuaternionicSymmetry.CompactSymplecticQuaternionicOrbit

/-! A concrete entrywise characterization of the actual projector
stabilizer: precisely the unitary-symplectic matrices with no mixed
coefficients between the first paired coordinates and their complement. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerBlocks

open Matrix CompactSymplecticHaar CompactSymplecticProjectiveQuotient
open scoped Matrix.Norms.Elementwise
noncomputable section

private abbrev Index (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- Membership in the first quaternionic coordinate pair. -/
def InFirstPair (n : ℕ) (i : Index n) : Prop :=
  i = Sum.inl (0 : Fin (n + 1)) ∨ i = Sum.inr (0 : Fin (n + 1))

/-- The actual commutant is characterized by vanishing of both mixed
matrix blocks. This is the first algebraic step toward identifying K with
the block subgroup `Sp(1) × Sp(n)`. -/
theorem mem_firstPairStabilizer_iff_mixed_zero (n : ℕ) (u : G n) :
    u ∈ firstPairStabilizer n ↔
      (∀ i j : Index n, InFirstPair n i → ¬InFirstPair n j →
        (u.1 : Matrix _ _ ℂ) i j = 0) ∧
      (∀ i j : Index n, ¬InFirstPair n i → InFirstPair n j →
        (u.1 : Matrix _ _ ℂ) i j = 0) := by
  classical
  constructor
  · intro hu
    constructor
    · intro i j hi hj
      change i = Sum.inl (0 : Fin (n + 1)) ∨ i = Sum.inr (0 : Fin (n + 1)) at hi
      change ¬(j = Sum.inl (0 : Fin (n + 1)) ∨ j = Sum.inr (0 : Fin (n + 1))) at hj
      have h := congrArg (fun A : Matrix (Index n) (Index n) ℂ => A i j) hu
      simpa [firstPairProjector, hi, hj] using h.symm
    · intro i j hi hj
      change ¬(i = Sum.inl (0 : Fin (n + 1)) ∨ i = Sum.inr (0 : Fin (n + 1))) at hi
      change j = Sum.inl (0 : Fin (n + 1)) ∨ j = Sum.inr (0 : Fin (n + 1)) at hj
      have h := congrArg (fun A : Matrix (Index n) (Index n) ℂ => A i j) hu
      simpa [firstPairProjector, hi, hj] using h
  · rintro ⟨hUpper, hLower⟩
    change (u.1 : Matrix _ _ ℂ) * firstPairProjector n =
      firstPairProjector n * (u.1 : Matrix _ _ ℂ)
    ext i j
    by_cases hi : InFirstPair n i <;> by_cases hj : InFirstPair n j
    · change i = Sum.inl (0 : Fin (n + 1)) ∨ i = Sum.inr (0 : Fin (n + 1)) at hi
      change j = Sum.inl (0 : Fin (n + 1)) ∨ j = Sum.inr (0 : Fin (n + 1)) at hj
      simp [firstPairProjector, hi, hj]
    · have hz := hUpper i j hi hj
      change i = Sum.inl (0 : Fin (n + 1)) ∨ i = Sum.inr (0 : Fin (n + 1)) at hi
      change ¬(j = Sum.inl (0 : Fin (n + 1)) ∨ j = Sum.inr (0 : Fin (n + 1))) at hj
      simp [firstPairProjector, hi, hj, hz]
    · have hz := hLower i j hi hj
      change ¬(i = Sum.inl (0 : Fin (n + 1)) ∨ i = Sum.inr (0 : Fin (n + 1))) at hi
      change j = Sum.inl (0 : Fin (n + 1)) ∨ j = Sum.inr (0 : Fin (n + 1)) at hj
      simp [firstPairProjector, hi, hj, hz]
    · change ¬(i = Sum.inl (0 : Fin (n + 1)) ∨ i = Sum.inr (0 : Fin (n + 1))) at hi
      change ¬(j = Sum.inl (0 : Fin (n + 1)) ∨ j = Sum.inr (0 : Fin (n + 1))) at hj
      simp [firstPairProjector, hi, hj]

end
end QuaternionicSymmetry.CompactSymplecticStabilizerBlocks
