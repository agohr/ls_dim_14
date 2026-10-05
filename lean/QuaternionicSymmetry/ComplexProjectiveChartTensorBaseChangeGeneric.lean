import QuaternionicSymmetry.ComplexProjectiveDiagonalAlgebraicCharts
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Maps

/-! A reusable tensor/quotient comparison for projective affine chart
polynomials over any complex coefficient algebra, including the literal
two-torus Laurent algebra. -/

namespace QuaternionicSymmetry.ComplexProjectiveChartTensorBaseChangeGeneric

open scoped TensorProduct
noncomputable section

variable (S : Type*) [CommRing S] [Algebra ℂ S] {d : ℕ}

def polynomialTensorEquiv :
    S ⊗[ℂ] MvPolynomial (Fin d) ℂ ≃ₐ[S] MvPolynomial (Fin d) S :=
  MvPolynomial.algebraTensorAlgEquiv ℂ S

theorem polynomialTensorEquiv_comp_includeRight :
    (polynomialTensorEquiv S (d := d)).toRingHom.comp
      (Algebra.TensorProduct.includeRight.toRingHom) =
    MvPolynomial.map (algebraMap ℂ S) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [polynomialTensorEquiv, MvPolynomial.algebraTensorAlgEquiv_tmul]
  · intro i
    simp [polynomialTensorEquiv, MvPolynomial.algebraTensorAlgEquiv_tmul]

def tensorExtendedIdeal (J : Ideal (MvPolynomial (Fin d) ℂ)) :
    Ideal (S ⊗[ℂ] MvPolynomial (Fin d) ℂ) :=
  Ideal.map Algebra.TensorProduct.includeRight.toRingHom J

def polynomialExtendedIdeal (J : Ideal (MvPolynomial (Fin d) ℂ)) :
    Ideal (MvPolynomial (Fin d) S) :=
  Ideal.map (MvPolynomial.map (algebraMap ℂ S)) J

theorem polynomialTensorEquiv_map_extendedIdeal
    (J : Ideal (MvPolynomial (Fin d) ℂ)) :
    (tensorExtendedIdeal S J).map (polynomialTensorEquiv S).toRingHom =
      polynomialExtendedIdeal S J := by
  rw [tensorExtendedIdeal, polynomialExtendedIdeal, Ideal.map_map]
  exact congrArg (fun f => Ideal.map f J)
    (polynomialTensorEquiv_comp_includeRight S)

def polynomialTensorQuotientEquiv
    (J : Ideal (MvPolynomial (Fin d) ℂ)) :
    ((S ⊗[ℂ] MvPolynomial (Fin d) ℂ) ⧸ tensorExtendedIdeal S J) ≃ₐ[S]
      (MvPolynomial (Fin d) S ⧸ polynomialExtendedIdeal S J) :=
  Ideal.quotientEquivAlg (tensorExtendedIdeal S J) (polynomialExtendedIdeal S J)
    (polynomialTensorEquiv S) (polynomialTensorEquiv_map_extendedIdeal S J).symm

def tensorQuotientProductEquiv (J : Ideal (MvPolynomial (Fin d) ℂ)) :
    ((S ⊗[ℂ] MvPolynomial (Fin d) ℂ) ⧸ tensorExtendedIdeal S J) ≃+*
      (S ⊗[ℂ] (MvPolynomial (Fin d) ℂ ⧸ J)) := by
  let P := MvPolynomial (Fin d) ℂ
  letI : Algebra P (S ⊗[ℂ] P) := Algebra.TensorProduct.rightAlgebra
  let e₁ : ((S ⊗[ℂ] P) ⧸ tensorExtendedIdeal S J) ≃+*
      ((S ⊗[ℂ] P) ⊗[P] (P ⧸ J)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (S ⊗[ℂ] P) J).toRingEquiv
  let e₂ : ((S ⊗[ℂ] P) ⊗[P] (P ⧸ J)) ≃+*
      ((P ⧸ J) ⊗[P] (S ⊗[ℂ] P)) :=
    (Algebra.TensorProduct.comm P (S ⊗[ℂ] P) (P ⧸ J)).toRingEquiv
  let e₃ : ((P ⧸ J) ⊗[P] (S ⊗[ℂ] P)) ≃+*
      ((P ⧸ J) ⊗[P] (P ⊗[ℂ] S)) :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : (P ⧸ J) ≃ₐ[P ⧸ J] (P ⧸ J))
      (Algebra.TensorProduct.commRight ℂ P S).symm).toRingEquiv
  let e₄ : ((P ⧸ J) ⊗[P] (P ⊗[ℂ] S)) ≃+*
      ((P ⧸ J) ⊗[ℂ] S) :=
    (Algebra.TensorProduct.cancelBaseChange ℂ P (P ⧸ J) (P ⧸ J) S).toRingEquiv
  let e₅ : ((P ⧸ J) ⊗[ℂ] S) ≃+* (S ⊗[ℂ] (P ⧸ J)) :=
    (Algebra.TensorProduct.comm ℂ (P ⧸ J) S).toRingEquiv
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

def chartFamilyProductRingEquiv (J : Ideal (MvPolynomial (Fin d) ℂ)) :
    (MvPolynomial (Fin d) S ⧸ polynomialExtendedIdeal S J) ≃+*
      (S ⊗[ℂ] (MvPolynomial (Fin d) ℂ ⧸ J)) :=
  (polynomialTensorQuotientEquiv S J).symm.toRingEquiv.trans
    (tensorQuotientProductEquiv S J)

end
end QuaternionicSymmetry.ComplexProjectiveChartTensorBaseChangeGeneric
