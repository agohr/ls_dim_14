import QuaternionicSymmetry.ComplexProjectiveTopology
import Mathlib.Analysis.SpecificLimits.Normed

/-! The explicit limiting vector obtained by damping every coordinate below
a maximal integral weight. Projectivization is the actual quotient map, and
closed-image membership follows by its continuity. No fixed-point or
weight-span statement is assumed. -/
namespace QuaternionicSymmetry.ComplexProjectiveMaximalWeightLimit

open ComplexProjectiveTopology Filter
open scoped Topology LinearAlgebra.Projectivization
noncomputable section

variable {d : ℕ}

def topPart (weights : Fin (d + 1) → ℤ) (m : ℤ) (v : Coord d) : Coord d :=
  fun i => if weights i = m then v i else 0

def dampedVector (weights : Fin (d + 1) → ℤ) (m : ℤ) (v : Coord d)
    (N : ℕ) : Coord d :=
  fun i => ((1 / 2 : ℂ) ^ N) ^ (m - weights i).toNat * v i

theorem topPart_ne_zero
    (weights : Fin (d + 1) → ℤ) (m : ℤ) (v : Coord d)
    (hTop : ∃ i, weights i = m ∧ v i ≠ 0) : topPart weights m v ≠ 0 := by
  obtain ⟨i,hi,hvi⟩ := hTop
  intro hz
  have := congrFun hz i
  simp [topPart,hi] at this
  exact hvi this

theorem dampedVector_ne_zero
    (weights : Fin (d + 1) → ℤ) (m : ℤ) (v : Coord d)
    (hTop : ∃ i, weights i = m ∧ v i ≠ 0) (N : ℕ) :
    dampedVector weights m v N ≠ 0 := by
  obtain ⟨i,hi,hvi⟩ := hTop
  intro hz
  have := congrFun hz i
  simp [dampedVector,hi] at this
  exact hvi this

theorem dampedVector_tendsto
    (weights : Fin (d + 1) → ℤ) (m : ℤ) (v : Coord d)
    (hMax : ∀ i, weights i ≤ m) :
    Tendsto (dampedVector weights m v) atTop (𝓝 (topPart weights m v)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  by_cases hi : weights i = m
  · simpa [dampedVector,topPart,hi] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => v i) atTop (𝓝 (v i)))
  · have hk : (m - weights i).toNat ≠ 0 := by
      have := hMax i
      omega
    have hhalf : Tendsto (fun N : ℕ => (1 / 2 : ℂ) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    simpa [dampedVector,topPart,hi,zero_pow hk] using
      (hhalf.pow (m - weights i).toNat).mul_const (v i)

theorem projective_dampedVector_tendsto
    (weights : Fin (d + 1) → ℤ) (m : ℤ) (v : Coord d)
    (hMax : ∀ i, weights i ≤ m) (hTop : ∃ i, weights i = m ∧ v i ≠ 0) :
    Tendsto (fun N : ℕ => Projectivization.mk ℂ (dampedVector weights m v N)
      (dampedVector_ne_zero weights m v hTop N)) atTop
      (𝓝 (Projectivization.mk ℂ (topPart weights m v) (topPart_ne_zero weights m v hTop))) := by
  have ht : Tendsto (fun N : ℕ =>
      (⟨dampedVector weights m v N, dampedVector_ne_zero weights m v hTop N⟩ :
        {w : Coord d // w ≠ 0})) atTop
      (𝓝 ⟨topPart weights m v,topPart_ne_zero weights m v hTop⟩) :=
    tendsto_subtype_rng.mpr (dampedVector_tendsto weights m v hMax)
  exact (continuous_mk d).continuousAt.tendsto.comp ht

theorem topPart_mem_closed
    (weights : Fin (d + 1) → ℤ) (m : ℤ) (v : Coord d)
    (hMax : ∀ i, weights i ≤ m) (hTop : ∃ i, weights i = m ∧ v i ≠ 0)
    (A : Set (Space d)) (hA : IsClosed A)
    (hOrbit : ∀ N : ℕ, Projectivization.mk ℂ (dampedVector weights m v N)
      (dampedVector_ne_zero weights m v hTop N) ∈ A) :
    Projectivization.mk ℂ (topPart weights m v) (topPart_ne_zero weights m v hTop) ∈ A :=
  hA.mem_of_tendsto (projective_dampedVector_tendsto weights m v hMax hTop)
    (Eventually.of_forall hOrbit)

end
end QuaternionicSymmetry.ComplexProjectiveMaximalWeightLimit
