import QuaternionicSymmetry.ToralEigenCharacter

/-! A common eigensubspace for commuting generators lies in one
generalized root space. One nonzero anchor vector defines the character;
no injectivity of the generator parametrization or diagonalizability
of the ambient adjoint module is needed. -/

namespace QuaternionicSymmetry.ToralCommonWeightRootInclusion

open AbelianLieSpanSubalgebra AbelianToralRootSpace ToralEigenCharacter
noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  (S : Set L) (hComm : ∀ x ∈ S, ∀ y ∈ S, ⁅x,y⁆ = 0)
  (W : Submodule ℂ L)
  (hEig : ∀ s ∈ S, ∃ c : ℂ, ∀ w ∈ W, ⁅s,w⁆ = c • w)
  (v₀ : L) (hv₀ : v₀ ∈ W) (hv₀ne : v₀ ≠ 0)

private def anchorEigen : ∀ s ∈ S, ∃ c : ℂ, ⁅s,v₀⁆ = c • v₀ := by
  intro s hs
  obtain ⟨c, hc⟩ := hEig s hs
  exact ⟨c, hc v₀ hv₀⟩

def anchorCharacter : H S hComm → ℂ :=
  eigenCharacter S hComm v₀ (anchorEigen S W hEig v₀ hv₀)

include hv₀ne

theorem anchorCharacter_add (x y : H S hComm) :
    anchorCharacter S hComm W hEig v₀ hv₀ (x+y) =
      anchorCharacter S hComm W hEig v₀ hv₀ x +
      anchorCharacter S hComm W hEig v₀ hv₀ y := by
  have hxy := bracket_eq_character S hComm v₀
    (anchorEigen S W hEig v₀ hv₀) (x+y)
  have hx := bracket_eq_character S hComm v₀
    (anchorEigen S W hEig v₀ hv₀) x
  have hy := bracket_eq_character S hComm v₀
    (anchorEigen S W hEig v₀ hv₀) y
  apply smul_left_injective ℂ hv₀ne
  calc
    anchorCharacter S hComm W hEig v₀ hv₀ (x+y) • v₀ =
        ⁅(↑(x+y) : L),v₀⁆ := hxy.symm
    _ = ⁅(x : L),v₀⁆ + ⁅(y : L),v₀⁆ := by simp [add_lie]
    _ = (anchorCharacter S hComm W hEig v₀ hv₀ x +
          anchorCharacter S hComm W hEig v₀ hv₀ y) • v₀ := by
      simp only [anchorCharacter, add_smul]
      rw [hx,hy]

theorem anchorCharacter_smul (a : ℂ) (x : H S hComm) :
    anchorCharacter S hComm W hEig v₀ hv₀ (a • x) =
      a * anchorCharacter S hComm W hEig v₀ hv₀ x := by
  have hax := bracket_eq_character S hComm v₀
    (anchorEigen S W hEig v₀ hv₀) (a • x)
  have hx := bracket_eq_character S hComm v₀
    (anchorEigen S W hEig v₀ hv₀) x
  apply smul_left_injective ℂ hv₀ne
  calc
    anchorCharacter S hComm W hEig v₀ hv₀ (a • x) • v₀ =
        ⁅(↑(a • x) : L),v₀⁆ := hax.symm
    _ = a • ⁅(x : L),v₀⁆ := by simp [smul_lie]
    _ = (a * anchorCharacter S hComm W hEig v₀ hv₀ x) • v₀ := by
      simp only [anchorCharacter, mul_smul]
      rw [hx]

theorem bracket_eq_anchorCharacter {x : L}
    (hx : x ∈ Submodule.span ℂ S) {w : L} (hw : w ∈ W) :
    ⁅x,w⁆ = anchorCharacter S hComm W hEig v₀ hv₀ ⟨x,hx⟩ • w := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨c, hc⟩ := hEig x hx
      have hα : anchorCharacter S hComm W hEig v₀ hv₀
          ⟨x, Submodule.subset_span hx⟩ = c :=
        eigenCharacter_eq_of_generator S hComm v₀
          (anchorEigen S W hEig v₀ hv₀) hv₀ne hx (hc v₀ hv₀)
      rw [hα]
      exact hc w hw
  | zero =>
      have hz := anchorCharacter_smul S hComm W hEig v₀ hv₀ hv₀ne
        0 (0 : H S hComm)
      have hz' : anchorCharacter S hComm W hEig v₀ hv₀ 0 = 0 := by
        simpa using hz
      simp only [zero_lie]
      change (0 : L) = anchorCharacter S hComm W hEig v₀ hv₀
        (0 : H S hComm) • w
      rw [hz']
      simp
  | add x y hx hy ihx ihy =>
      rw [add_lie, ihx, ihy]
      simp only [← add_smul]
      congr 1
      exact (anchorCharacter_add S hComm W hEig v₀ hv₀ hv₀ne
        ⟨x,hx⟩ ⟨y,hy⟩).symm
  | smul a x hx ihx =>
      rw [smul_lie, ihx]
      simp only [← mul_smul]
      congr 1
      exact (anchorCharacter_smul S hComm W hEig v₀ hv₀ hv₀ne a ⟨x,hx⟩).symm

theorem submodule_le_exactWeightSpace :
    W ≤ (LieModule.weightSpace L
      (anchorCharacter S hComm W hEig v₀ hv₀) : Submodule ℂ L) := by
  intro w hw
  change w ∈ LieModule.weightSpace L
    (anchorCharacter S hComm W hEig v₀ hv₀)
  rw [LieModule.mem_weightSpace]
  intro x
  exact bracket_eq_anchorCharacter S hComm W hEig v₀ hv₀ hv₀ne x.2 hw

theorem submodule_le_rootSpace :
    letI := H_isNilpotent S hComm
    W ≤ (LieAlgebra.rootSpace (H S hComm)
      (anchorCharacter S hComm W hEig v₀ hv₀) : Submodule ℂ L) := by
  exact le_trans
    (submodule_le_exactWeightSpace S hComm W hEig v₀ hv₀ hv₀ne)
    (exactWeightSpace_le_rootSpace S hComm
      (anchorCharacter S hComm W hEig v₀ hv₀))

end
end QuaternionicSymmetry.ToralCommonWeightRootInclusion
