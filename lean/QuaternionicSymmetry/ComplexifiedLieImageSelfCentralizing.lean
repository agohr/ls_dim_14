import QuaternionicSymmetry.ComplexifiedLieCentralizerComponents
import QuaternionicSymmetry.ComplexifiedLieBracketTransfer
import QuaternionicSymmetry.LieCentralizerTransport

/-! A self-centralizing abelian real Lie subspace remains self-centralizing
after a bracket-preserving bijective complexification. In the twistor
application, the bijection is precisely the reviewed NT-C infinitesimal
complexification, not an arbitrary model-identification premise. -/

namespace QuaternionicSymmetry.ComplexifiedLieImageSelfCentralizing

open ComplexifiedLieCentralizerComponents
open ComplexifiedLieBracketTransfer
open LieCentralizerTransport
open RealToComplexTangentComplexification
open scoped TensorProduct
noncomputable section

variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L]
  [LieRing V] [LieAlgebra ℂ V]

theorem image_selfCentralizing
    (T : Submodule ℝ L)
    (hAb : ∀ x ∈ T, ∀ y ∈ T, ⁅x,y⁆ = 0)
    (hSelf : ∀ x : L, (∀ t ∈ T, ⁅x,t⁆ = 0) → x ∈ T)
    (f : L →ₗ[ℝ] V)
    (hBij : Function.Bijective (complexifiedMapComplex f))
    (hBracket : ∀ x y : L, f ⁅x,y⁆ = ⁅f x,f y⁆)
    (z : V) :
    z ∈ (complexSpan T).map (complexifiedMapComplex f) ↔
      ∀ w ∈ (complexSpan T).map (complexifiedMapComplex f), ⁅z,w⁆ = 0 := by
  exact map_selfCentralizing (complexifiedMapComplex f) hBij
    (complexifiedMapComplex_map_lie f hBracket)
    (complexSpan T) (complexSpan_selfCentralizing_full T hAb hSelf) z

end
end QuaternionicSymmetry.ComplexifiedLieImageSelfCentralizing
