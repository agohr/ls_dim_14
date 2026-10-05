import QuaternionicSymmetry.CompactRepresentationTriviality

/-! Triviality propagation using local frames only. A globally continuous
choice of frame is neither required nor inferred. The local representations
must describe the same intrinsic predicate on every chart. -/

namespace QuaternionicSymmetry.CompactRepresentationLocalTriviality

open CompactRepresentationTrivialLocus CompactRepresentationTriviality
noncomputable section

variable {G A X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableMul G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [TopologicalSpace X]

/-- A local-frame presentation of the intrinsic triviality predicate. -/
def LocalPresentations (P : X → Prop) : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ ρ : U → G →* A,
      Continuous (fun p : G × U => ρ p.2 p.1) ∧
      ∀ y : U, P y.1 ↔ ∀ g, ρ y g = 1

theorem isClopen_of_localPresentations (P : X → Prop)
    (hlocal : LocalPresentations (G := G) (A := A) P) :
    IsClopen {x | P x} := by
  have hopen : IsOpen {x | P x} := by
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    obtain ⟨U,hU,hxU,ρ,hρ,heq⟩ := hlocal x
    have hT := isOpen_trivialLocus (μ := probability (G := G))
      ρ hρ (integrable_family ρ hρ)
    refine ⟨Subtype.val '' trivialLocus ρ, ?_, hU.isOpenMap_subtype_val _ hT, ?_⟩
    · rintro y ⟨z,hz,rfl⟩
      exact (heq z).mpr hz
    · exact ⟨⟨x,hxU⟩,(heq ⟨x,hxU⟩).mp hx,rfl⟩
  have hcompl : IsOpen {x | ¬ P x} := by
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    obtain ⟨U,hU,hxU,ρ,hρ,heq⟩ := hlocal x
    have hT := (isClosed_trivialLocus ρ hρ).isOpen_compl
    refine ⟨Subtype.val '' (trivialLocus ρ)ᶜ, ?_,
      hU.isOpenMap_subtype_val _ hT, ?_⟩
    · rintro y ⟨z,hz,rfl⟩ hy
      exact hz ((heq z).mp hy)
    · exact ⟨⟨x,hxU⟩,fun h => hx ((heq ⟨x,hxU⟩).mpr h),rfl⟩
  exact ⟨isOpen_compl_iff.mp hcompl,hopen⟩

theorem everywhere_of_localPresentations [PreconnectedSpace X]
    (P : X → Prop) (hlocal : LocalPresentations (G := G) (A := A) P)
    (x₀ : X) (hx₀ : P x₀) : ∀ x, P x := by
  have h := (isClopen_of_localPresentations P hlocal).eq_univ ⟨x₀,hx₀⟩
  intro x
  change x ∈ {x | P x}
  rw [h]
  trivial

end
end QuaternionicSymmetry.CompactRepresentationLocalTriviality
