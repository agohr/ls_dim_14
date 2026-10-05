import QuaternionicSymmetry.TorusIntegralCocharacter
import QuaternionicSymmetry.ComplexProjectiveDiagonalAction
import QuaternionicSymmetry.ComplexProjectiveMaximalWeightLimit

/-! The damped maximal-weight limit is the projective limit of an actual
integral cocharacter orbit. A closed invariant image therefore contains it.
The surviving block is fixed by that cocharacter; if its full weights agree,
it is fixed by the entire torus. -/
namespace QuaternionicSymmetry.ComplexProjectiveCocharacterLimit

open ComplexProjectiveTopology TorusLaurentRepresentation TorusIntegralCocharacter
open ComplexProjectiveDiagonalAction ComplexProjectiveMaximalWeightLimit
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {r d : ℕ}

def twoUnit : ℂˣ := Units.mk0 2 (by norm_num)

theorem dampedVector_eq_normalized_orbit
    (μ : Fin (d + 1) → Fin r → ℤ) (u : Fin r → ℤ) (m : ℤ)
    (hMax : ∀ i, pairing (μ i) u ≤ m) (v : Coord d) (N : ℕ) :
    dampedVector (fun i => pairing (μ i) u) m v N =
      (((twoUnit ^ N) ^ (-m) : ℂˣ) : ℂ) •
        diagonalEquiv μ (cocharacter u (twoUnit ^ N)) v := by
  have hhalf : (((twoUnit ^ N)⁻¹ : ℂˣ) : ℂ) = (1 / 2 : ℂ) ^ N := by
    simp [twoUnit, inv_pow, one_div]
  ext i
  change ((1 / 2 : ℂ) ^ N) ^ (m - pairing (μ i) u).toNat * v i =
    (((twoUnit ^ N) ^ (-m) : ℂˣ) : ℂ) *
      ((complexWeightCharacter (μ i) (cocharacter u (twoUnit ^ N)) : ℂ) * v i)
  rw [← hhalf, ← normalized_character (μ i) u m (hMax i) (twoUnit ^ N)]
  ring

theorem projective_dampedVector_eq_orbit
    (μ : Fin (d + 1) → Fin r → ℤ) (u : Fin r → ℤ) (m : ℤ)
    (hMax : ∀ i, pairing (μ i) u ≤ m) (v : Coord d) (hv : v ≠ 0)
    (hTop : ∃ i, pairing (μ i) u = m ∧ v i ≠ 0) (N : ℕ) :
    Projectivization.mk ℂ (dampedVector (fun i => pairing (μ i) u) m v N)
      (dampedVector_ne_zero _ m v hTop N) =
    projectiveAction μ (cocharacter u (twoUnit ^ N)) (Projectivization.mk ℂ v hv) := by
  rw [projectiveAction_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨(twoUnit ^ N) ^ (-m), ?_⟩
  simpa [Units.smul_def] using
    (dampedVector_eq_normalized_orbit μ u m hMax v N).symm

theorem topPart_mem_of_invariant
    (μ : Fin (d + 1) → Fin r → ℤ) (u : Fin r → ℤ) (m : ℤ)
    (hMax : ∀ i, pairing (μ i) u ≤ m) (v : Coord d) (hv : v ≠ 0)
    (hTop : ∃ i, pairing (μ i) u = m ∧ v i ≠ 0)
    (A : Set (Space d)) (hA : IsClosed A)
    (hInvariant : ∀ z : ComplexTorus r, Set.MapsTo (projectiveAction μ z) A A)
    (hvA : Projectivization.mk ℂ v hv ∈ A) :
    Projectivization.mk ℂ (topPart (fun i => pairing (μ i) u) m v)
      (topPart_ne_zero _ m v hTop) ∈ A := by
  apply topPart_mem_closed _ m v hMax hTop A hA
  intro N
  rw [projective_dampedVector_eq_orbit μ u m hMax v hv hTop N]
  exact hInvariant _ hvA

theorem topPart_fixed_by_cocharacter
    (μ : Fin (d + 1) → Fin r → ℤ) (u : Fin r → ℤ) (m : ℤ)
    (v : Coord d) (hTop : ∃ i, pairing (μ i) u = m ∧ v i ≠ 0)
    (z : ℂˣ) :
    projectiveAction μ (cocharacter u z)
      (Projectivization.mk ℂ (topPart (fun i => pairing (μ i) u) m v)
        (topPart_ne_zero _ m v hTop)) =
      Projectivization.mk ℂ (topPart (fun i => pairing (μ i) u) m v)
        (topPart_ne_zero _ m v hTop) := by
  rw [projectiveAction_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨z ^ m, ?_⟩
  ext i
  by_cases hi : pairing (μ i) u = m
  · simp [Units.smul_def, diagonalEquiv_apply, topPart, hi, character_cocharacter]
  · simp [Units.smul_def, diagonalEquiv_apply, topPart, hi]

theorem topPart_fixed_by_torus
    (μ : Fin (d + 1) → Fin r → ℤ) (u ν : Fin r → ℤ) (m : ℤ)
    (hFace : ∀ i, pairing (μ i) u = m → μ i = ν)
    (v : Coord d) (hTop : ∃ i, pairing (μ i) u = m ∧ v i ≠ 0)
    (z : ComplexTorus r) :
    projectiveAction μ z
      (Projectivization.mk ℂ (topPart (fun i => pairing (μ i) u) m v)
        (topPart_ne_zero _ m v hTop)) =
      Projectivization.mk ℂ (topPart (fun i => pairing (μ i) u) m v)
        (topPart_ne_zero _ m v hTop) := by
  rw [projectiveAction_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨complexWeightCharacter ν z, ?_⟩
  ext i
  by_cases hi : pairing (μ i) u = m
  · simp [Units.smul_def, diagonalEquiv_apply, topPart, hi, hFace i hi]
  · simp [Units.smul_def, diagonalEquiv_apply, topPart, hi]

end
end QuaternionicSymmetry.ComplexProjectiveCocharacterLimit
