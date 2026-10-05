import QuaternionicSymmetry.ComplexProjectiveDiagonalChartLocus
import Mathlib.RingTheory.Ideal.Maps

/-! The polynomial ideal of each actual standard affine chart locus is
stable under every diagonal torus specialization. This is the local
ideal needed for a projective closed-subscheme action. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartVanishingIdeal

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalHolomorphic
open ComplexProjectiveDiagonalChartLocus
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def chartVanishingIdeal (A : Set (Space d)) (i : Fin (d + 1)) :
    Ideal (MvPolynomial (Fin d) ℂ) :=
  ⨅ w : chartLocus A i,
    RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id ℂ) w.1)

theorem mem_chartVanishingIdeal_iff
    (A : Set (Space d)) (i : Fin (d + 1))
    (p : MvPolynomial (Fin d) ℂ) :
    p ∈ chartVanishingIdeal A i ↔
      ∀ w : Fin d → ℂ, w ∈ chartLocus A i →
        MvPolynomial.eval w p = 0 := by
  simp [chartVanishingIdeal, MvPolynomial.eval_eq]

def chartSubstitution (μ : Fin (d + 1) → Fin r → ℤ)
    (z : ComplexTorus r) (i : Fin (d + 1)) :
    MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin d) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun k => MvPolynomial.C
      ((complexWeightCharacter (μ (i.succAbove k)) z : ℂ) /
        (complexWeightCharacter (μ i) z : ℂ)) * MvPolynomial.X k)

theorem eval_chartSubstitution
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (i : Fin (d + 1)) (w : Fin d → ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    MvPolynomial.eval w (chartSubstitution μ z i p) =
      MvPolynomial.eval (chartDiagonal μ z i w) p := by
  have h := MvPolynomial.comp_eval₂Hom MvPolynomial.C
    (fun k => MvPolynomial.C
      ((complexWeightCharacter (μ (i.succAbove k)) z : ℂ) /
        (complexWeightCharacter (μ i) z : ℂ)) * MvPolynomial.X k)
    (MvPolynomial.eval₂Hom (RingHom.id ℂ) w)
  change ((MvPolynomial.eval₂Hom (RingHom.id ℂ) w).comp
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun k => MvPolynomial.C
        ((complexWeightCharacter (μ (i.succAbove k)) z : ℂ) /
          (complexWeightCharacter (μ i) z : ℂ)) * MvPolynomial.X k))) p = _
  rw [h]
  have hc : (MvPolynomial.eval₂Hom (RingHom.id ℂ) w).comp
      MvPolynomial.C = RingHom.id ℂ := by
    ext c
    simp
  have hx : (fun k => MvPolynomial.eval₂Hom (RingHom.id ℂ) w
      (MvPolynomial.C
        ((complexWeightCharacter (μ (i.succAbove k)) z : ℂ) /
          (complexWeightCharacter (μ i) z : ℂ)) * MvPolynomial.X k)) =
      chartDiagonal μ z i w := by
    funext k
    simp [chartDiagonal]
  rw [hc, hx]
  rfl

theorem chartSubstitution_mem_chartVanishingIdeal
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (A : Set (Space d))
    (hA : Set.MapsTo (projectiveAction μ z) A A)
    (i : Fin (d + 1))
    {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ chartVanishingIdeal A i) :
    chartSubstitution μ z i p ∈ chartVanishingIdeal A i := by
  rw [mem_chartVanishingIdeal_iff] at hp ⊢
  intro w hw
  rw [eval_chartSubstitution]
  exact hp _ (chartDiagonal_maps_chartLocus μ z A hA i hw)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartVanishingIdeal
