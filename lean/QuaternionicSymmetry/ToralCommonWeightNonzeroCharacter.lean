import QuaternionicSymmetry.ToralCommonWeightRootInclusion

/-! If one generator has a nonzero common eigenvalue on a nonzero
weight subspace, its anchor-defined root character is nonzero. -/

namespace QuaternionicSymmetry.ToralCommonWeightNonzeroCharacter

open AbelianToralRootSpace ToralEigenCharacter
open ToralCommonWeightRootInclusion
noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  (S : Set L) (hComm : ∀ x ∈ S, ∀ y ∈ S, ⁅x,y⁆ = 0)
  (W : Submodule ℂ L)
  (hEig : ∀ s ∈ S, ∃ c : ℂ, ∀ w ∈ W, ⁅s,w⁆ = c • w)
  (v₀ : L) (hv₀ : v₀ ∈ W) (hv₀ne : v₀ ≠ 0)

include hv₀ne

theorem anchorCharacter_ne_zero_of_generator
    {s : L} (hs : s ∈ S) {c : ℂ} (hc : ∀ w ∈ W, ⁅s,w⁆ = c • w)
    (hcnz : c ≠ 0) :
    anchorCharacter S hComm W hEig v₀ hv₀ ≠ 0 := by
  intro hzero
  have hbr := bracket_eq_anchorCharacter S hComm W hEig v₀ hv₀ hv₀ne
    (Submodule.subset_span hs) hv₀
  have hval : anchorCharacter S hComm W hEig v₀ hv₀
      ⟨s, Submodule.subset_span hs⟩ = c := by
    apply smul_left_injective ℂ hv₀ne
    exact (hbr.symm.trans (hc v₀ hv₀))
  apply hcnz
  simpa [hzero] using hval.symm

end
end QuaternionicSymmetry.ToralCommonWeightNonzeroCharacter
