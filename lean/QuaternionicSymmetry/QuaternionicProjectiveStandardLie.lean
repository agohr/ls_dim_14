import QuaternionicSymmetry.QuaternionicProjectiveStandardAdjoint
import QuaternionicSymmetry.QuaternionicLieAlgebraProjection

/-! The infinitesimal standard representation on the Hilbert sum.  The
imaginary quaternion acts on the extra quaternionic line on the right with
the negative sign forced by the group action `w ↦ w * star q`. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveStandardLie

open QuaternionicProjectiveStandardL2 QuaternionicLieAlgebraProjection
  QuaternionicProjectiveStandardHilbertStructure
open scoped Quaternion
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

private def imaginaryLinear : (Fin 3 → ℝ) →ₗ[ℝ] ℍ where
  toFun a := ⟨0, a 0, a 1, a 2⟩
  map_add' a b := by ext <;> simp
  map_smul' r a := by ext <;> simp

def imaginary : (Fin 3 → ℝ) →L[ℝ] ℍ :=
  imaginaryLinear.toContinuousLinearMap

@[simp] theorem imaginary_re (a : Fin 3 → ℝ) : (imaginary a).re = 0 := rfl
@[simp] theorem imaginary_imI (a : Fin 3 → ℝ) : (imaginary a).imI = a 0 := rfl
@[simp] theorem imaginary_imJ (a : Fin 3 → ℝ) : (imaginary a).imJ = a 1 := rfl
@[simp] theorem imaginary_imK (a : Fin 3 → ℝ) : (imaginary a).imK = a 2 := rfl

def scalarLineLie (S : QuaternionicStructure E) :
    (E →L[ℝ] E) →L[ℝ] (ℍ →L[ℝ] ℍ) :=
  (((ContinuousLinearMap.mul ℝ ℍ).flip).comp (-imaginary)).comp
    (axialProjection.comp (ManifoldQuaternionicAdjointConnection.adjointRepresentation S))

def standardLie (S : QuaternionicStructure E) :
    (E →L[ℝ] E) →L[ℝ]
      (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) :=
  let L : (E →L[ℝ] E) →ₗ[ℝ]
      (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := {
    toFun A :=
      let c := WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ
      c.symm.toContinuousLinearMap.comp
        (((symplecticProjection S A).prodMap (scalarLineLie S A)).comp
          c.toContinuousLinearMap)
    map_add' := by
      intro A B
      ext z
      apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
      apply Prod.ext <;> simp [map_add]
    map_smul' := by
      intro r A
      ext z
      apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
      apply Prod.ext <;> simp [map_smul]
  }
  L.toContinuousLinearMap

theorem standardLie_blocks (S : QuaternionicStructure E)
    (A : E →L[ℝ] E) (z : StandardSpace (E := E)) :
    (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) (standardLie S A z) =
      ((symplecticProjection S A)
          ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z).1,
        (scalarLineLie S A)
          ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z).2) := rfl

theorem standardLie_commutes_I (S : QuaternionicStructure E)
    (A : E →L[ℝ] E)
    (hI : ∀ v, symplecticProjection S A (S.I v) =
      S.I (symplecticProjection S A v))
    (z : StandardSpace (E := E)) :
    standardLie S A ((standardStructure S).I z) =
      (standardStructure S).I (standardLie S A z) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · change symplecticProjection S A (S.I z.fst) =
      S.I (symplecticProjection S A z.fst)
    exact hI _
  · change (QuaternionicUnitQuaternionTransport.basisI * z.snd) *
      (-(imaginary (axialProjection
        (ManifoldQuaternionicAdjointConnection.adjointRepresentation S A)))) =
      QuaternionicUnitQuaternionTransport.basisI *
        (z.snd * (-(imaginary (axialProjection
          (ManifoldQuaternionicAdjointConnection.adjointRepresentation S A)))))
    rw [mul_assoc]

theorem standardLie_commutes_J (S : QuaternionicStructure E)
    (A : E →L[ℝ] E)
    (hJ : ∀ v, symplecticProjection S A (S.J v) =
      S.J (symplecticProjection S A v))
    (z : StandardSpace (E := E)) :
    standardLie S A ((standardStructure S).J z) =
      (standardStructure S).J (standardLie S A z) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · change symplecticProjection S A (S.J z.fst) =
      S.J (symplecticProjection S A z.fst)
    exact hJ _
  · change (QuaternionicUnitQuaternionTransport.basisJ * z.snd) *
      (-(imaginary (axialProjection
        (ManifoldQuaternionicAdjointConnection.adjointRepresentation S A)))) =
      QuaternionicUnitQuaternionTransport.basisJ *
        (z.snd * (-(imaginary (axialProjection
          (ManifoldQuaternionicAdjointConnection.adjointRepresentation S A)))))
    rw [mul_assoc]

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardLie
