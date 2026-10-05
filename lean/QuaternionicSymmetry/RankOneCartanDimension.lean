import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The rank-one dimension estimate from the internally formalized root
system of a Lie algebra with nondegenerate Killing form. -/
namespace QuaternionicSymmetry.RankOneCartanDimension
open LieAlgebra LieModule Module
noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

theorem center_eq_bot_of_small_selfCentralizer (H : LieSubalgebra ℂ L)
    (hH : finrank ℂ H ≤ 1) (hL : 1 < finrank ℂ L)
    (hSelf : ∀ z : L, z ∈ H ↔ ∀ w ∈ H, ⁅z,w⁆ = 0) :
    center ℂ L = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  change z = 0
  by_contra hzne
  have hzcomm : ∀ w : L, ⁅w,z⁆ = 0 := (LieModule.mem_maxTrivSubmodule ℂ L L z).mp hz
  have hzH : z ∈ H := (hSelf z).2 (fun w _ => by rw [← lie_skew,hzcomm,neg_zero])
  have hzneH : (⟨z,hzH⟩ : H) ≠ 0 := fun h => hzne (congrArg Subtype.val h)
  have hpos : 0 < finrank ℂ H := finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨z,hzH⟩,hzneH⟩
  have hdim : finrank ℂ H = 1 := by omega
  have hspan := (finrank_eq_one_iff_of_nonzero' (⟨z,hzH⟩ : H)
    hzneH).mp hdim
  have htop : H = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    apply (hSelf y).2
    intro w hw
    obtain ⟨c,hc⟩ := hspan ⟨w,hw⟩
    have hw' : c • z = w := congrArg Subtype.val hc
    rw [← hw',lie_smul,hzcomm,smul_zero]
  have heq : finrank ℂ H = finrank ℂ L := by
    rw [htop]
    exact (LieSubalgebra.topEquiv : (⊤ : LieSubalgebra ℂ L) ≃ₗ⁅ℂ⁆ L).toLinearEquiv.finrank_eq
  omega

theorem finrank_le_three_of_rank_one_cartan
    [IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (hH : finrank ℂ H ≤ 1) : finrank ℂ L ≤ 3 := by
  classical
  by_cases hex : ∃ α : Weight ℂ H L, α.IsNonZero
  · obtain ⟨α,hα⟩ := hex
    have ha : (α : H →ₗ[ℂ] ℂ) ≠ 0 := Weight.coe_toLinear_ne_zero_iff.mpr hα
    have hdual : finrank ℂ (H →ₗ[ℂ] ℂ) = 1 := by
      have hpos : 0 < finrank ℂ (H →ₗ[ℂ] ℂ) :=
        finrank_pos_iff_exists_ne_zero.mpr ⟨(α : H →ₗ[ℂ] ℂ),ha⟩
      have hd : finrank ℂ (H →ₗ[ℂ] ℂ) = finrank ℂ H := by simp
      omega
    have hroots (β : Weight ℂ H L) (hβ : β.IsNonZero) : β = -α ∨ β = α := by
      obtain ⟨c,hc⟩ := (finrank_eq_one_iff_of_nonzero' (α : H →ₗ[ℂ] ℂ) ha).mp hdual
        (β : H →ₗ[ℂ] ℂ)
      apply IsKilling.eq_neg_or_eq_of_eq_smul α β hβ c
      exact congrArg DFunLike.coe hc.symm
    let A := (rootSpace H α).toSubmodule
    let B := (rootSpace H (-α)).toSubmodule
    have htop : H.toSubmodule ⊔ A ⊔ B = ⊤ := by
      have ht := cartan_sup_iSup_rootSpace_eq_top H
      apply eq_top_iff.mpr
      rw [← LieSubmodule.top_toSubmodule (R := ℂ) (L := H) (M := L), ← ht,
        LieSubmodule.sup_toSubmodule, LieSubmodule.iSup_toSubmodule]
      apply sup_le
      · exact le_sup_of_le_left le_sup_left
      · apply iSup_le
        intro β
        rw [LieSubmodule.iSup_toSubmodule]
        apply iSup_le
        intro hβ
        rcases hroots β hβ with rfl | rfl
        · exact le_sup_right
        · exact le_sup_of_le_left le_sup_right
    have hA : finrank ℂ A = 1 := IsKilling.finrank_rootSpace_eq_one α hα
    have hB : finrank ℂ B = 1 := IsKilling.finrank_rootSpace_eq_one (-α) hα.neg
    have h₁ := Submodule.finrank_add_le_finrank_add_finrank H.toSubmodule A
    have h₂ := Submodule.finrank_add_le_finrank_add_finrank (H.toSubmodule ⊔ A) B
    rw [htop,finrank_top] at h₂
    change finrank ℂ H ≤ 1 at hH
    change finrank ℂ (↥(H.toSubmodule ⊔ A)) ≤ finrank ℂ H + finrank ℂ A at h₁
    omega
  · have ht : H.toLieSubmodule = ⊤ := by
      have h := cartan_sup_iSup_rootSpace_eq_top H
      have hz : (⨆ α : Weight ℂ H L, ⨆ (_ : α.IsNonZero), rootSpace H α) = ⊥ := by
        apply eq_bot_iff.mpr
        exact iSup_le (fun α => iSup_le (fun hα => (hex ⟨α,hα⟩).elim))
      rwa [hz,sup_bot_eq] at h
    have hd : finrank ℂ H = finrank ℂ L := by
      change finrank ℂ H.toLieSubmodule.toSubmodule = _
      rw [ht,LieSubmodule.top_toSubmodule,finrank_top]
    omega

end
end QuaternionicSymmetry.RankOneCartanDimension
