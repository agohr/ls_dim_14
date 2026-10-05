import QuaternionicSymmetry.QuaternionicOperatorMatrix

/-! The fixed matrix realization is real linear, so it applies coefficientwise
to quaternionic curvature forms. -/
namespace QuaternionicSymmetry.QuaternionicOperatorMatrixLinear
open QuaternionicOperatorMatrix QuaternionicMatrixCoordinates QuaternionicMatrixModel
open scoped Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)

theorem operatorMatrix_add (A B : E →ₗ[ℝ] E)
    (hA : ∀ v, A (S.I v) = S.I (A v))
    (hB : ∀ v, B (S.I v) = S.I (B v))
    (hAB : ∀ v, (A + B) (S.I v) = S.I ((A + B) v)) :
    operatorMatrix S (A + B) hAB = operatorMatrix S A hA + operatorMatrix S B hB := by
  apply Matrix.toEuclideanLin.injective
  simp only [operatorMatrix, matrixEnd, map_add, LinearEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro v
  change (modelEnd S (A + B)) v = modelEnd S A v + modelEnd S B v
  simp [modelEnd]

theorem operatorMatrix_smul (r : ℝ) (A : E →ₗ[ℝ] E)
    (hA : ∀ v, A (S.I v) = S.I (A v))
    (hrA : ∀ v, (r • A) (S.I v) = S.I ((r • A) v)) :
    operatorMatrix S (r • A) hrA = r • operatorMatrix S A hA := by
  apply Matrix.toEuclideanLin.injective
  rw [← Complex.coe_smul r (operatorMatrix S A hA)]
  simp only [operatorMatrix, matrixEnd, map_smul, LinearEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.smul_apply, Complex.coe_smul]
  change (modelEnd S (r • A)) v = r • modelEnd S A v
  simp [modelEnd]

def skewMatrixMap : S.skewCentralizer →ₗ[ℝ]
    Matrix (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension)
      (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension) ℂ where
  toFun A := operatorMatrix S A.val
    ((S.mem_skewCentralizer_iff A.val).mp A.property).2.1
  map_add' A B := operatorMatrix_add S A.val B.val _ _ _
  map_smul' r A := operatorMatrix_smul S r A.val _ _

def hermitianMatrixMap : S.skewCentralizer →ₗ[ℝ]
    hermitianAntiSelfDualSubmodule S.quaternionicDimension :=
  ((Complex.I • skewMatrixMap S).codRestrict _ (by
    intro A
    have h := (S.mem_skewCentralizer_iff A.val).mp A.property
    exact operatorMatrix_hermitianAntiSelfDual S A.val h.2.1 h.2.2
      (fun v w => by rw [h.1 v w]; exact neg_add_cancel _)))

theorem skewMatrixMap_injective : Function.Injective (skewMatrixMap S) := by
  intro A B h
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  apply (QuaternionicCanonicalModel.canonicalModel S).injective
  have ha := operatorMatrix_action S A.val
    ((S.mem_skewCentralizer_iff A.val).mp A.property).2.1 v
  have hb := operatorMatrix_action S B.val
    ((S.mem_skewCentralizer_iff B.val).mp B.property).2.1 v
  change realMatrixAction (skewMatrixMap S A)
    (QuaternionicCanonicalModel.canonicalModel S v) = _ at ha
  change realMatrixAction (skewMatrixMap S B)
    (QuaternionicCanonicalModel.canonicalModel S v) = _ at hb
  exact ha.symm.trans ((congrArg
    (fun T => realMatrixAction T (QuaternionicCanonicalModel.canonicalModel S v)) h).trans hb)

end
end QuaternionicSymmetry.QuaternionicOperatorMatrixLinear
