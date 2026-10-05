import QuaternionicSymmetry.ContinuousWedge
import QuaternionicSymmetry.ContinuousAlternationTransport
import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-! Full alternation absorbs an alternation inside either block of a
concatenated multilinear product, with the expected block factorial. -/

namespace QuaternionicSymmetry.ContinuousWedgeBlockAlternation

open AlternatingMap

variable {E A B : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
  {p q : ℕ}

theorem domCoprod_alternatization_left
    (f : MultilinearMap ℝ (fun _ : Fin p => E) A)
    (g : MultilinearMap ℝ (fun _ : Fin q => E) B) :
    MultilinearMap.alternatization
      (MultilinearMap.domCoprod (MultilinearMap.alternatization f) g) =
    (p.factorial : ℝ) •
      MultilinearMap.alternatization (MultilinearMap.domCoprod f g) := by
  rw [MultilinearMap.domCoprod_alternization,
    AlternatingMap.coe_alternatization]
  rw [MultilinearMap.domCoprod_alternization]
  rw [← AlternatingMap.domCoprod'_apply, ← TensorProduct.smul_tmul',
    LinearMap.map_smul_of_tower]
  simp only [Fintype.card_fin, Nat.cast_smul_eq_nsmul,
    AlternatingMap.domCoprod'_apply]

theorem domCoprod_alternatization_right
    (f : MultilinearMap ℝ (fun _ : Fin p => E) A)
    (g : MultilinearMap ℝ (fun _ : Fin q => E) B) :
    MultilinearMap.alternatization
      (MultilinearMap.domCoprod f (MultilinearMap.alternatization g)) =
    (q.factorial : ℝ) •
      MultilinearMap.alternatization (MultilinearMap.domCoprod f g) := by
  rw [MultilinearMap.domCoprod_alternization,
    AlternatingMap.coe_alternatization]
  rw [MultilinearMap.domCoprod_alternization]
  rw [← AlternatingMap.domCoprod'_apply, TensorProduct.tmul_smul,
    LinearMap.map_smul_of_tower]
  simp only [Fintype.card_fin, Nat.cast_smul_eq_nsmul,
    AlternatingMap.domCoprod'_apply]

end QuaternionicSymmetry.ContinuousWedgeBlockAlternation

namespace QuaternionicSymmetry.ContinuousWedgeBlockAlternation

open QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousMultilinearProduct
  QuaternionicSymmetry.ContinuousAlternationTransport
open scoped TensorProduct

noncomputable section

variable {E A B C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  {p q : ℕ}

private def tensorPair (P : A →L[ℝ] B →L[ℝ] C) : (A ⊗[ℝ] B) →ₗ[ℝ] C :=
  TensorProduct.lift <| LinearMap.mk₂ ℝ (fun a b => P a b)
    (by intro a a' b; simp)
    (by intro r a b; simp)
    (by intro a b b'; simp)
    (by intro r a b; simp)

private theorem tensorPair_tmul (P : A →L[ℝ] B →L[ℝ] C) (a : A) (b : B) :
    tensorPair P (a ⊗ₜ[ℝ] b) = P a b := rfl

private theorem concatenate_toMultilinearMap (P : A →L[ℝ] B →L[ℝ] C)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) B) :
    (concatenate P f g).toMultilinearMap =
      (tensorPair P).compMultilinearMap
        (MultilinearMap.domCoprod f.toMultilinearMap g.toMultilinearMap) := by
  ext v
  simp [concatenate_apply, MultilinearMap.domCoprod_apply, tensorPair_tmul,
    Function.comp_def]

theorem alternation_concatenate_left (P : A →L[ℝ] B →L[ℝ] C)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) B) :
    ContinuousMultilinearMap.alternatization
      (concatenate P (alternationCLM f).toContinuousMultilinearMap g) =
      (p.factorial : ℝ) •
        ContinuousMultilinearMap.alternatization (concatenate P f g) := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  simp only [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap,
    ContinuousAlternatingMap.toAlternatingMap_smul]
  rw [concatenate_toMultilinearMap, concatenate_toMultilinearMap]
  rw [LinearMap.compMultilinearMap_alternatization,
    LinearMap.compMultilinearMap_alternatization]
  have hinner : (alternationCLM f).toContinuousMultilinearMap.toMultilinearMap =
      (MultilinearMap.alternatization f.toMultilinearMap :
        MultilinearMap ℝ (fun _ : Fin p => E) A) := by
    ext v
    simp [alternationCLM_apply, MultilinearMap.alternatization_apply,
      Function.comp_def]
  rw [hinner]
  rw [domCoprod_alternatization_left]
  rw [LinearMap.compAlternatingMap_smul]

theorem alternation_concatenate_right (P : A →L[ℝ] B →L[ℝ] C)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) B) :
    ContinuousMultilinearMap.alternatization
      (concatenate P f (alternationCLM g).toContinuousMultilinearMap) =
      (q.factorial : ℝ) •
        ContinuousMultilinearMap.alternatization (concatenate P f g) := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  simp only [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap,
    ContinuousAlternatingMap.toAlternatingMap_smul]
  rw [concatenate_toMultilinearMap, concatenate_toMultilinearMap]
  rw [LinearMap.compMultilinearMap_alternatization,
    LinearMap.compMultilinearMap_alternatization]
  have hinner : (alternationCLM g).toContinuousMultilinearMap.toMultilinearMap =
      (MultilinearMap.alternatization g.toMultilinearMap :
        MultilinearMap ℝ (fun _ : Fin q => E) B) := by
    ext v
    simp [alternationCLM_apply, MultilinearMap.alternatization_apply,
      Function.comp_def]
  rw [hinner]
  rw [domCoprod_alternatization_right]
  rw [LinearMap.compAlternatingMap_smul]

theorem alternation_concatenate_left_fin (P : A →L[ℝ] B →L[ℝ] C)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) B) :
    alternationCLM ((concatenate P (alternationCLM f).toContinuousMultilinearMap g).domDomCongr
      (finSumFinEquiv (m := p) (n := q))) =
    (p.factorial : ℝ) • alternationCLM
      ((concatenate P f g).domDomCongr
        (finSumFinEquiv (m := p) (n := q))) := by
  ext v
  simp only [alternationCLM_domDomCongr_apply,
    ContinuousAlternatingMap.smul_apply]
  exact congrArg (fun ω : E [⋀^Fin p ⊕ Fin q]→L[ℝ] C =>
    ω (v ∘ finSumFinEquiv)) (alternation_concatenate_left P f g)

theorem alternation_concatenate_right_fin (P : A →L[ℝ] B →L[ℝ] C)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) B) :
    alternationCLM ((concatenate P f (alternationCLM g).toContinuousMultilinearMap).domDomCongr
      (finSumFinEquiv (m := p) (n := q))) =
    (q.factorial : ℝ) • alternationCLM
      ((concatenate P f g).domDomCongr
        (finSumFinEquiv (m := p) (n := q))) := by
  ext v
  simp only [alternationCLM_domDomCongr_apply,
    ContinuousAlternatingMap.smul_apply]
  exact congrArg (fun ω : E [⋀^Fin p ⊕ Fin q]→L[ℝ] C =>
    ω (v ∘ finSumFinEquiv)) (alternation_concatenate_right P f g)

end
end QuaternionicSymmetry.ContinuousWedgeBlockAlternation
