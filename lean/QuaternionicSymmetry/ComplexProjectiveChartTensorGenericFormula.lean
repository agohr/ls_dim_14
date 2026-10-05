import QuaternionicSymmetry.ComplexProjectiveChartTensorBaseChangeGeneric

/-! Exact pure-tensor formula for the generic polynomial-chart quotient
product equivalence, including the literal double-torus coefficient ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveChartTensorGenericFormula

open ComplexProjectiveChartTensorBaseChangeGeneric
open scoped TensorProduct
noncomputable section

variable (S : Type*) [CommRing S] [Algebra ℂ S] {d : ℕ}

theorem tensorQuotientProductEquiv_mk_tmul
    (J : Ideal (MvPolynomial (Fin d) ℂ))
    (s : S) (p : MvPolynomial (Fin d) ℂ) :
    tensorQuotientProductEquiv S J
      (Ideal.Quotient.mk (tensorExtendedIdeal S J) (s ⊗ₜ[ℂ] p)) =
    s ⊗ₜ[ℂ] (Ideal.Quotient.mk J p) := by
  let P := MvPolynomial (Fin d) ℂ
  let B := S ⊗[ℂ] P
  letI : Algebra P B := Algebra.TensorProduct.rightAlgebra
  let e₁ : (B ⧸ tensorExtendedIdeal S J) ≃+* B ⊗[P] (P ⧸ J) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toRingEquiv
  let e₂ : B ⊗[P] (P ⧸ J) ≃+* (P ⧸ J) ⊗[P] B :=
    (Algebra.TensorProduct.comm P B (P ⧸ J)).toRingEquiv
  let e₃ : (P ⧸ J) ⊗[P] B ≃+* (P ⧸ J) ⊗[P] (P ⊗[ℂ] S) :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : (P ⧸ J) ≃ₐ[P ⧸ J] (P ⧸ J))
      (Algebra.TensorProduct.commRight ℂ P S).symm).toRingEquiv
  let e₄ : (P ⧸ J) ⊗[P] (P ⊗[ℂ] S) ≃+* (P ⧸ J) ⊗[ℂ] S :=
    (Algebra.TensorProduct.cancelBaseChange ℂ P (P ⧸ J) (P ⧸ J) S).toRingEquiv
  let e₅ : (P ⧸ J) ⊗[ℂ] S ≃+* S ⊗[ℂ] (P ⧸ J) :=
    (Algebra.TensorProduct.comm ℂ (P ⧸ J) S).toRingEquiv
  change e₅ (e₄ (e₃ (e₂ (e₁
    (Ideal.Quotient.mk (tensorExtendedIdeal S J) (s ⊗ₜ[ℂ] p)))))) = _
  have h₁ : e₁ (Ideal.Quotient.mk (tensorExtendedIdeal S J)
      (s ⊗ₜ[ℂ] p)) = (s ⊗ₜ[ℂ] p) ⊗ₜ[P] (1 : P ⧸ J) :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk B J _
  rw [h₁]
  rw [show e₂ ((s ⊗ₜ[ℂ] p) ⊗ₜ[P] (1 : P ⧸ J)) =
      (1 : P ⧸ J) ⊗ₜ[P] (s ⊗ₜ[ℂ] p) from rfl]
  change (Algebra.TensorProduct.comm ℂ (P ⧸ J) S)
    ((Algebra.TensorProduct.cancelBaseChange ℂ P (P ⧸ J) (P ⧸ J) S)
      ((Algebra.TensorProduct.congr
        (AlgEquiv.refl : (P ⧸ J) ≃ₐ[P ⧸ J] (P ⧸ J))
        (Algebra.TensorProduct.commRight ℂ P S).symm)
        ((1 : P ⧸ J) ⊗ₜ[P] (s ⊗ₜ[ℂ] p)))) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change (Algebra.TensorProduct.comm ℂ (P ⧸ J) S)
    ((Algebra.TensorProduct.cancelBaseChange ℂ P (P ⧸ J) (P ⧸ J) S)
      ((1 : P ⧸ J) ⊗ₜ[P] (p ⊗ₜ[ℂ] s))) = _
  simp [Algebra.smul_def]
  rfl

theorem chartFamilyProductRingEquiv_baseChanged
    (J : Ideal (MvPolynomial (Fin d) ℂ))
    (s : S) (p : MvPolynomial (Fin d) ℂ) :
    chartFamilyProductRingEquiv S J
      (Ideal.Quotient.mk (polynomialExtendedIdeal S J)
        (s • MvPolynomial.map (algebraMap ℂ S) p)) =
    s ⊗ₜ[ℂ] Ideal.Quotient.mk J p := by
  let q := Ideal.Quotient.mk (tensorExtendedIdeal S J) (s ⊗ₜ[ℂ] p)
  have hq : polynomialTensorQuotientEquiv S J q =
      Ideal.Quotient.mk (polynomialExtendedIdeal S J)
        (s • MvPolynomial.map (algebraMap ℂ S) p) := by
    simp [q, polynomialTensorQuotientEquiv, polynomialTensorEquiv]
  rw [← hq]
  have hs : (polynomialTensorQuotientEquiv S J).symm.toRingEquiv
      ((polynomialTensorQuotientEquiv S J) q) = q := by
    exact (polynomialTensorQuotientEquiv S J).symm_apply_apply q
  simp only [chartFamilyProductRingEquiv, RingEquiv.trans_apply, hs]
  exact tensorQuotientProductEquiv_mk_tmul S J s p

end
end QuaternionicSymmetry.ComplexProjectiveChartTensorGenericFormula
