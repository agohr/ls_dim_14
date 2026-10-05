import QuaternionicSymmetry.SpanningCharactersSeparateImage
import Mathlib.LinearAlgebra.Pi

/-! A real-spanning family of literal integral weight vectors separates
complex coordinate vectors by its complexified dot products. This is a
finite-dimensional algebra statement; no geometric weight-span premise is
asserted. -/

namespace QuaternionicSymmetry.IntegralWeightRealSpanComplexSeparation

noncomputable section

def realWeightVector {r : ℕ} (μ : Fin r → ℤ) : Fin r → ℝ :=
  fun j => (μ j : ℝ)

def complexWeightDot {r : ℕ} (μ : Fin r → ℤ) (z : Fin r → ℂ) : ℂ :=
  ∑ j, (μ j : ℂ) * z j

theorem complexWeightDot_separates_of_real_span {r : ℕ} {ι : Type*}
    (μ : ι → Fin r → ℤ)
    (hSpan : Submodule.span ℝ (Set.range (fun i => realWeightVector (μ i))) = ⊤)
    (z : Fin r → ℂ)
    (hz : ∀ i, complexWeightDot (μ i) z = 0) : z = 0 := by
  classical
  let Rz : (Fin r → ℝ) → ℂ := fun a => ∑ j, (a j : ℂ) * z j
  have hR (a : Fin r → ℝ)
      (ha : a ∈ Submodule.span ℝ (Set.range (fun i => realWeightVector (μ i)))) :
      Rz a = 0 := by
    induction ha using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨i,rfl⟩ := ha
        exact hz i
    | zero => simp [Rz]
    | add a b ha hb iha ihb =>
        dsimp [Rz] at *
        simp only [Pi.add_apply, Complex.ofReal_add, add_mul,
          Finset.sum_add_distrib, iha, ihb, add_zero]
    | smul c a ha iha =>
        dsimp [Rz] at *
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
          mul_assoc, ← Finset.mul_sum, iha, mul_zero]
  funext j
  have hj : Rz (Pi.single j 1) = 0 := hR _ (by rw [hSpan]; trivial)
  have hsingle : Rz (Pi.single j 1) = z j := by
    dsimp [Rz]
    simp only [Pi.single_apply]
    have hterm (x : Fin r) :
        ((if x = j then (1 : ℝ) else 0 : ℝ) : ℂ) * z x =
          if x = j then z x else 0 := by
      split_ifs <;> simp
    simp_rw [hterm]
    simp
  exact hsingle.symm.trans hj

end
end QuaternionicSymmetry.IntegralWeightRealSpanComplexSeparation
