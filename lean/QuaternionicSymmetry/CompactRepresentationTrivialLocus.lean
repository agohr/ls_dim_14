import QuaternionicSymmetry.CompactRepresentationNearIdentity
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Connected.Clopen

/-! Triviality is both open and closed in a continuous family of
representations of a compact group. The open direction is proved by
compact projection and averaging, not by assuming local constancy of
character multiplicities. -/

namespace QuaternionicSymmetry.CompactRepresentationTrivialLocus

open MeasureTheory MeasureTheory.Measure
open CompactRepresentationNearIdentity
noncomputable section

variable {G A X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [MeasurableMul G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [TopologicalSpace X]
  {μ : Measure G} [IsProbabilityMeasure μ] [IsMulLeftInvariant μ]

def trivialLocus (ρ : X → G →* A) : Set X := {x | ∀ g, ρ x g = 1}

omit [CompactSpace G] [MeasurableSpace G] [MeasurableMul G]
  [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem isClosed_trivialLocus (ρ : X → G →* A)
    (hρ : Continuous (fun p : G × X => ρ p.2 p.1)) :
    IsClosed (trivialLocus ρ) := by
  have heq : trivialLocus ρ = ⋂ g : G, {x | ρ x g = 1} := by
    ext x
    simp [trivialLocus]
  rw [heq]
  exact isClosed_iInter (fun g => isClosed_eq
    (hρ.comp (continuous_const.prodMk continuous_id)) continuous_const)

theorem isOpen_trivialLocus (ρ : X → G →* A)
    (hρ : Continuous (fun p : G × X => ρ p.2 p.1))
    (hint : ∀ x, Integrable (fun g => ρ x g) μ) :
    IsOpen (trivialLocus ρ) := by
  let B : Set (G × X) := {p | (1/2 : ℝ) ≤ ‖ρ p.2 p.1 - 1‖}
  have hB : IsClosed B :=
    isClosed_le continuous_const ((hρ.sub continuous_const).norm)
  have hopen : IsOpen ((Prod.snd '' B)ᶜ) :=
    (isClosedMap_snd_of_compactSpace B hB).isOpen_compl
  have heq : trivialLocus ρ = (Prod.snd '' B)ᶜ := by
    ext x
    constructor
    · intro hx
      rintro ⟨⟨g,y⟩, hgy, rfl⟩
      change (1/2 : ℝ) ≤ ‖ρ y g - 1‖ at hgy
      rw [hx g, sub_self, norm_zero] at hgy
      norm_num at hgy
    · intro hx
      have hsmall (g : G) : ‖ρ x g - 1‖ ≤ (1/2 : ℝ) := by
        apply le_of_lt
        apply lt_of_not_ge
        intro h
        exact hx ⟨(g,x), h, rfl⟩
      exact representation_eq_one_of_uniform_small (ρ x) (hint x)
        (by norm_num : (1/2 : ℝ) < 1) hsmall
  rwa [heq]

theorem trivial_everywhere_of_trivial_at [PreconnectedSpace X]
    (ρ : X → G →* A)
    (hρ : Continuous (fun p : G × X => ρ p.2 p.1))
    (hint : ∀ x, Integrable (fun g => ρ x g) μ)
    (x₀ : X) (hx₀ : ∀ g, ρ x₀ g = 1) : ∀ x g, ρ x g = 1 := by
  have hall : trivialLocus ρ = Set.univ :=
    (show IsClopen (trivialLocus ρ) from
      ⟨isClosed_trivialLocus ρ hρ, isOpen_trivialLocus ρ hρ hint⟩).eq_univ ⟨x₀,hx₀⟩
  intro x
  have hx : x ∈ trivialLocus ρ := by rw [hall]; trivial
  exact hx

end
end QuaternionicSymmetry.CompactRepresentationTrivialLocus
