import QuaternionicSymmetry.ComplexProjectiveTorusPreservation
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Ideal.Maps

/-! The diagonal substitution preserves the actual polynomial ideal of
the affine cone over any invariant projective set. This is literal ideal
stability, not a claim that the analytic twistor is already a Proj scheme. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalVanishingIdeal

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveTorusPreservation
open TorusLaurentRepresentation
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {r d : ℕ}

def affineCone (A : Set (Space d)) : Set (Coord d) :=
  {v | v = 0 ∨ ∃ hv : v ≠ 0, Projectivization.mk ℂ v hv ∈ A}

def evalAt (v : Coord d) :
    MvPolynomial (Fin (d + 1)) ℂ →+* ℂ :=
  MvPolynomial.eval₂Hom (RingHom.id ℂ) v

def vanishingIdeal (A : Set (Space d)) :
    Ideal (MvPolynomial (Fin (d + 1)) ℂ) :=
  ⨅ v : affineCone A, RingHom.ker (evalAt v.1)

theorem mem_vanishingIdeal_iff (A : Set (Space d))
    (p : MvPolynomial (Fin (d + 1)) ℂ) :
    p ∈ vanishingIdeal A ↔
      ∀ v : Coord d, v ∈ affineCone A →
        MvPolynomial.eval v p = 0 := by
  simp [vanishingIdeal, evalAt, MvPolynomial.eval_eq]

def diagonalSubstitution
    (μ : Fin (d + 1) → Fin r → ℤ) (z : TorusLaurentRepresentation.ComplexTorus r) :
    MvPolynomial (Fin (d + 1)) ℂ →+*
      MvPolynomial (Fin (d + 1)) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => MvPolynomial.C
      (complexWeightCharacter (μ i) z : ℂ) * MvPolynomial.X i)

theorem eval_diagonalSubstitution
    (μ : Fin (d + 1) → Fin r → ℤ)
    (z : TorusLaurentRepresentation.ComplexTorus r)
    (v : Coord d) (p : MvPolynomial (Fin (d + 1)) ℂ) :
    MvPolynomial.eval v (diagonalSubstitution μ z p) =
      MvPolynomial.eval (diagonalEquiv μ z v) p := by
  change evalAt v (diagonalSubstitution μ z p) =
    evalAt (diagonalEquiv μ z v) p
  have h := MvPolynomial.comp_eval₂Hom
    MvPolynomial.C
    (fun i => MvPolynomial.C
      (complexWeightCharacter (μ i) z : ℂ) * MvPolynomial.X i)
    (evalAt v)
  change ((evalAt v).comp
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i => MvPolynomial.C
        (complexWeightCharacter (μ i) z : ℂ) * MvPolynomial.X i))) p = _
  rw [h]
  have hc : (evalAt v).comp MvPolynomial.C = RingHom.id ℂ := by
    ext c
    simp [evalAt]
  have hx : (fun i => (evalAt v)
      (MvPolynomial.C (complexWeightCharacter (μ i) z : ℂ) * MvPolynomial.X i)) =
      diagonalEquiv μ z v := by
    funext i
    simp [evalAt]
  rw [hc, hx]
  rfl

theorem diagonal_maps_affineCone
    (μ : Fin (d + 1) → Fin r → ℤ)
    (z : TorusLaurentRepresentation.ComplexTorus r)
    (A : Set (Space d))
    (hA : Set.MapsTo (projectiveAction μ z) A A) :
    Set.MapsTo (diagonalEquiv μ z) (affineCone A) (affineCone A) := by
  intro v hv
  rcases hv with hv | ⟨hne,hv⟩
  · left
    simp [hv]
  · right
    refine ⟨(diagonalEquiv μ z).map_ne_zero_iff.mpr hne, ?_⟩
    rw [← projectiveAction_mk μ z v hne]
    exact hA hv

theorem diagonalSubstitution_mem_vanishingIdeal
    (μ : Fin (d + 1) → Fin r → ℤ)
    (z : TorusLaurentRepresentation.ComplexTorus r)
    (A : Set (Space d))
    (hA : Set.MapsTo (projectiveAction μ z) A A)
    {p : MvPolynomial (Fin (d + 1)) ℂ}
    (hp : p ∈ vanishingIdeal A) :
    diagonalSubstitution μ z p ∈ vanishingIdeal A := by
  rw [mem_vanishingIdeal_iff] at hp ⊢
  intro v hv
  rw [eval_diagonalSubstitution]
  exact hp _ (diagonal_maps_affineCone μ z A hA hv)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalVanishingIdeal
