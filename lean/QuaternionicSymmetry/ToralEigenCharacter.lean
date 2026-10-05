import QuaternionicSymmetry.AbelianToralRootSpace

/-! A nonzero common eigenvector for commuting Lie generators defines its
own character on their complex span. This avoids requiring injectivity of
the generator parametrization: scalar uniqueness makes the character
well-defined on the actual Lie subalgebra. -/

namespace QuaternionicSymmetry.ToralEigenCharacter

open AbelianLieSpanSubalgebra AbelianToralRootSpace
noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  (S : Set L) (hComm : ∀ x ∈ S, ∀ y ∈ S, ⁅x,y⁆ = 0)
  (v : L) (hEigen : ∀ s ∈ S, ∃ c : ℂ, ⁅s,v⁆ = c • v)

include hEigen

theorem scalarExists_span {x : L} (hx : x ∈ Submodule.span ℂ S) :
    ∃ c : ℂ, ⁅x,v⁆ = c • v := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hEigen x hx
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by simp [add_lie, ha, hb, add_smul]⟩
  | smul a x hx ihx =>
      obtain ⟨b, hb⟩ := ihx
      exact ⟨a * b, by simp [smul_lie, hb, mul_smul]⟩

def eigenCharacter :
    AbelianToralRootSpace.H S hComm → ℂ :=
  fun x => Classical.choose (scalarExists_span S v hEigen x.2)

theorem bracket_eq_character (x : AbelianToralRootSpace.H S hComm) :
    ⁅(x : L),v⁆ = eigenCharacter S hComm v hEigen x • v :=
  Classical.choose_spec (scalarExists_span S v hEigen x.2)

theorem eigenCharacter_eq_of_generator (hv : v ≠ 0)
    {s : L} (hs : s ∈ S) {c : ℂ} (hc : ⁅s,v⁆ = c • v) :
    eigenCharacter S hComm v hEigen ⟨s, Submodule.subset_span hs⟩ = c := by
  have he := bracket_eq_character S hComm v hEigen
    (⟨s, Submodule.subset_span hs⟩ : AbelianToralRootSpace.H S hComm)
  rw [hc] at he
  exact smul_left_injective ℂ hv he.symm

theorem mem_exactWeightSpace :
    v ∈ LieModule.weightSpace L (eigenCharacter S hComm v hEigen) := by
  rw [LieModule.mem_weightSpace]
  exact bracket_eq_character S hComm v hEigen

theorem mem_rootSpace :
    letI := AbelianToralRootSpace.H_isNilpotent S hComm
    v ∈ LieAlgebra.rootSpace (AbelianToralRootSpace.H S hComm)
      (eigenCharacter S hComm v hEigen) := by
  exact (AbelianToralRootSpace.exactWeightSpace_le_rootSpace S hComm
    (eigenCharacter S hComm v hEigen))
      (mem_exactWeightSpace S hComm v hEigen)

end
end QuaternionicSymmetry.ToralEigenCharacter
