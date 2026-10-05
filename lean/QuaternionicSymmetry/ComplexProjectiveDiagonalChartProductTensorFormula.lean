import QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductRing

/-! Explicit pure-tensor value of the actual quotient/product equivalence. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductTensorFormula

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartTensorQuotient
open ComplexProjectiveDiagonalChartProductRing
open scoped TensorProduct
noncomputable section


variable {r d : ℕ}

theorem chartTensorQuotientProductEquiv_mk_tmul
    (A : Set (Space d)) (i : Fin (d + 1))
    (t : TorusCoordinateRing r) (p : MvPolynomial (Fin d) ℂ) :
    chartTensorQuotientProductEquiv (r := r) A i
      (Ideal.Quotient.mk (tensorExtendedChartIdeal (r := r) A i)
        (t ⊗ₜ[ℂ] p)) =
      t ⊗ₜ[ℂ] (Ideal.Quotient.mk (chartVanishingIdeal A i) p) := by
  let P := MvPolynomial (Fin d) ℂ
  let T := TorusCoordinateRing r
  let I := chartVanishingIdeal A i
  let B := T ⊗[ℂ] P
  letI : Algebra P B := Algebra.TensorProduct.rightAlgebra
  let e₁ : (B ⧸ tensorExtendedChartIdeal (r := r) A i) ≃+*
      B ⊗[P] (P ⧸ I) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toRingEquiv
  let e₂ : B ⊗[P] (P ⧸ I) ≃+* (P ⧸ I) ⊗[P] B :=
    (Algebra.TensorProduct.comm P B (P ⧸ I)).toRingEquiv
  let e₃ : (P ⧸ I) ⊗[P] B ≃+* (P ⧸ I) ⊗[P] (P ⊗[ℂ] T) :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : (P ⧸ I) ≃ₐ[P ⧸ I] (P ⧸ I))
      (Algebra.TensorProduct.commRight ℂ P T).symm).toRingEquiv
  let e₄ : (P ⧸ I) ⊗[P] (P ⊗[ℂ] T) ≃+* (P ⧸ I) ⊗[ℂ] T :=
    (Algebra.TensorProduct.cancelBaseChange ℂ P (P ⧸ I) (P ⧸ I) T).toRingEquiv
  let e₅ : (P ⧸ I) ⊗[ℂ] T ≃+* T ⊗[ℂ] (P ⧸ I) :=
    (Algebra.TensorProduct.comm ℂ (P ⧸ I) T).toRingEquiv
  change e₅ (e₄ (e₃ (e₂ (e₁
    (Ideal.Quotient.mk (tensorExtendedChartIdeal (r := r) A i)
      (t ⊗ₜ[ℂ] p)))))) = _
  have h₁ : e₁ (Ideal.Quotient.mk (tensorExtendedChartIdeal (r := r) A i)
      (t ⊗ₜ[ℂ] p)) = (t ⊗ₜ[ℂ] p) ⊗ₜ[P] (1 : P ⧸ I) :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk B I _
  rw [h₁]
  rw [show e₂ ((t ⊗ₜ[ℂ] p) ⊗ₜ[P] (1 : P ⧸ I)) =
      (1 : P ⧸ I) ⊗ₜ[P] (t ⊗ₜ[ℂ] p) from rfl]
  change (Algebra.TensorProduct.comm ℂ (P ⧸ I) T)
    ((Algebra.TensorProduct.cancelBaseChange ℂ P (P ⧸ I) (P ⧸ I) T)
      ((Algebra.TensorProduct.congr
        (AlgEquiv.refl : (P ⧸ I) ≃ₐ[P ⧸ I] (P ⧸ I))
        (Algebra.TensorProduct.commRight ℂ P T).symm)
        ((1 : P ⧸ I) ⊗ₜ[P] (t ⊗ₜ[ℂ] p)))) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change (Algebra.TensorProduct.comm ℂ (P ⧸ I) T)
    ((Algebra.TensorProduct.cancelBaseChange ℂ P (P ⧸ I) (P ⧸ I) T)
      ((1 : P ⧸ I) ⊗ₜ[P] (p ⊗ₜ[ℂ] t))) = _
  simp [Algebra.smul_def, I]
  rfl

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductTensorFormula
