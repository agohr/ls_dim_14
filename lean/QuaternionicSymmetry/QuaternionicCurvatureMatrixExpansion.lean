import QuaternionicSymmetry.QuaternionicCurvatureFiniteExpansion
import QuaternionicSymmetry.QuaternionicOperatorMatrixLinear
import QuaternionicSymmetry.QuaternionicProjectiveStandardHilbertStructure
import QuaternionicSymmetry.OperatorBlockDerivative

/-! The finite curvature expansion in source-normalized Hermitian
quaternionic matrices, including the zero quaternionic line. -/
namespace QuaternionicSymmetry.QuaternionicCurvatureMatrixExpansion
open QuaternionicCurvatureFiniteExpansion QuaternionicProjectiveStandardL2
open QuaternionicProjectiveStandardHilbertStructure QuaternionicOperatorMatrixLinear
open QuaternionicMatrixModel
open scoped Quaternion
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance

def upperEmbedding : (E →L[ℝ] E) →ₗ[ℝ]
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) where
  toFun A := OperatorBlockDerivative.blockOperator
    (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) A 0
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro z
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
    apply Prod.ext
    · rfl
    · change (0 : ℍ) = 0 + 0
      simp
  map_smul' r A := by
    apply ContinuousLinearMap.ext
    intro z
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
    apply Prod.ext
    · rfl
    · change (0 : ℍ) = r • (0 : ℍ)
      simp

omit [FiniteDimensional ℝ E] in
theorem upperEmbedding_mem (S : QuaternionicStructure E) (A : operatorSpace S) :
    (upperEmbedding A.val).toLinearMap ∈ (standardStructure S).skewCentralizer := by
  have hA := (S.mem_skewCentralizer_iff _).mp A.property
  apply ((standardStructure S).mem_skewCentralizer_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro z w
    change inner ℝ (A.val z.fst) w.fst + inner ℝ (0 : ℍ) w.snd =
      -(inner ℝ z.fst (A.val w.fst) + inner ℝ z.snd (0 : ℍ))
    simpa only [inner_zero_left, inner_zero_right, add_zero] using hA.1 z.fst w.fst
  · intro z
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
    apply Prod.ext
    · exact hA.2.1 z.fst
    · change (0 : ℍ) = leftLineStructure.I 0
      rw [map_zero]
  · intro z
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
    apply Prod.ext
    · exact hA.2.2 z.fst
    · change (0 : ℍ) = leftLineStructure.J 0
      rw [map_zero]

def upperCentralizerMap (S : QuaternionicStructure E) :
    operatorSpace S →ₗ[ℝ] (standardStructure S).skewCentralizer :=
  ((ContinuousLinearMap.coeLM ℝ).comp
    (upperEmbedding.comp (operatorSpace S).subtype)).codRestrict _ (upperEmbedding_mem S)

def sourceMatrixMap (S : QuaternionicStructure E) : operatorSpace S →ₗ[ℝ]
    hermitianAntiSelfDualSubmodule (standardStructure S).quaternionicDimension :=
  (1 / (2 * Real.pi) : ℝ) •
    ((hermitianMatrixMap (standardStructure S)).comp (upperCentralizerMap S))

theorem sourceMatrix_expansion (S : QuaternionicStructure E)
    (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (hR : ∀ u v, (R u v).toLinearMap ∈ S.skewCentralizer) (u v : E) :
    ∑ a : Index S, coefficient S R hR a u v • sourceMatrixMap S (operatorBasis S a) =
      sourceMatrixMap S ⟨R u v, hR u v⟩ := by
  have h := congrArg (sourceMatrixMap S) ((operatorBasis S).sum_repr ⟨R u v, hR u v⟩)
  simpa only [map_sum, map_smul, coefficient_apply] using h

end
end QuaternionicSymmetry.QuaternionicCurvatureMatrixExpansion
