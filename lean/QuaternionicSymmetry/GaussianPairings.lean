import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
  Finite algebraic Wick contractions.

  This is a polynomial identity for a Kronecker delta and finite sums.  It
  contains no measure or probabilistic assumption.
-/

namespace QuaternionicSymmetry
namespace GaussianPairings

open Finset BigOperators

variable {ι S : Type*} [DecidableEq ι] [CommRing S]

/-- The Kronecker delta with values in a commutative ring. -/
def delta (i j : ι) : S := if i = j then 1 else 0

@[simp] theorem delta_self (i : ι) : delta i i = (1 : S) := by
  simp [delta]

@[simp] theorem delta_ne {i j : ι} (h : i ≠ j) : delta i j = (0 : S) := by
  simp [delta, h]

section

variable [Fintype ι]

private theorem sum_delta_mul (i : ι) (f : ι → S) :
    ∑ j, delta i j * f j = f i := by
  simp [delta]

private theorem sum_mul_delta (i : ι) (f : ι → S) :
    ∑ j, f j * delta i j = f i := by
  simpa [mul_comm] using sum_delta_mul i f

theorem pairing_ij_kl (θ : ι → S) :
    ∑ i, ∑ j, ∑ k, ∑ l,
      delta i j * delta k l * θ i * θ j * θ k * θ l = (∑ i, θ i ^ 2) ^ 2 := by
  simp [delta, pow_two, mul_left_comm, mul_comm]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pairing_ik_jl (θ : ι → S) :
    ∑ i, ∑ j, ∑ k, ∑ l,
      delta i k * delta j l * θ i * θ j * θ k * θ l = (∑ i, θ i ^ 2) ^ 2 := by
  simp [delta, pow_two, mul_left_comm, mul_comm]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pairing_il_jk (θ : ι → S) :
    ∑ i, ∑ j, ∑ k, ∑ l,
      delta i l * delta j k * θ i * θ j * θ k * θ l = (∑ i, θ i ^ 2) ^ 2 := by
  simp [delta, pow_two, mul_left_comm, mul_comm]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The three finite Wick contractions give three copies of the quadratic square. -/
theorem fourth_pairing (θ : ι → S) :
    ∑ i, ∑ j, ∑ k, ∑ l,
      (delta i j * delta k l + delta i k * delta j l + delta i l * delta j k) *
        θ i * θ j * θ k * θ l = 3 * (∑ i, θ i ^ 2) ^ 2 := by
  calc
    _ = (∑ i, ∑ j, ∑ k, ∑ l, delta i j * delta k l * θ i * θ j * θ k * θ l) +
          (∑ i, ∑ j, ∑ k, ∑ l, delta i k * delta j l * θ i * θ j * θ k * θ l) +
          (∑ i, ∑ j, ∑ k, ∑ l, delta i l * delta j k * θ i * θ j * θ k * θ l) := by
      simp only [add_mul, Finset.sum_add_distrib]
    _ = _ := by
      rw [pairing_ij_kl, pairing_ik_jl, pairing_il_jk]
      ring

end
end GaussianPairings
end QuaternionicSymmetry
