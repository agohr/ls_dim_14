import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-! Compact actions admit invariant open neighborhoods inside every open
neighborhood of a fixed point. The local version also applies in a chart. -/
namespace QuaternionicSymmetry.CompactActionInvariantNeighborhood
open Set

variable {K X : Type*} [Group K] [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace X]

def invariantCore (a : K × X → X) (U : Set X) : Set X :=
  {x | ∀ g, a (g,x) ∈ U}

lemma invariantCore_open {a : K × X → X} {U V : Set X}
    (hU : IsOpen U) (ha : ContinuousOn a (univ ×ˢ U))
    (hV : IsOpen V) (hVU : V ⊆ U)
    (h1 : ∀ x, x ∈ U → a (1,x) = x) :
    IsOpen (U ∩ invariantCore a V) := by
  let O := (univ ×ˢ U) ∩ a ⁻¹' V
  have hO : IsOpen O := ha.isOpen_inter_preimage (isOpen_univ.prod hU) hV
  have hc := (isClosedMap_snd_of_compactSpace (X := K) (Y := X)) _ hO.isClosed_compl
  have heq : U ∩ invariantCore a V = (Prod.snd '' Oᶜ)ᶜ := by
    ext x
    constructor
    · rintro ⟨hx,hall⟩ ⟨⟨g,y⟩,hbad,rfl⟩
      exact hbad ⟨⟨mem_univ _,hx⟩,hall g⟩
    · intro hx
      have hall : ∀ g, (g,x) ∈ O := by
        intro g
        by_contra hg
        exact hx ⟨(g,x),hg,rfl⟩
      exact ⟨(hall 1).1.2,fun g => (hall g).2⟩
  rw [heq]
  exact hc.isOpen_compl

lemma invariantCore_subset {a : K × X → X} {U V : Set X}
    (h1 : ∀ x, x ∈ U → a (1,x) = x) :
    U ∩ invariantCore a V ⊆ V := by
  intro x hx
  simpa only [h1 x hx.1] using hx.2 1

lemma invariantCore_invariant {a : K × X → X} {U V : Set X}
    (hVU : V ⊆ U)
    (hmul : ∀ g h x, x ∈ U → a (g,a (h,x)) = a (g*h,x))
    {x : X} (hx : x ∈ U ∩ invariantCore a V) (h : K) :
    a (h,x) ∈ U ∩ invariantCore a V := by
  refine ⟨hVU (hx.2 h),?_⟩
  intro g
  rw [hmul g h x hx.1]
  exact hx.2 (g*h)

lemma fixed_mem_invariantCore {a : K × X → X} {U V : Set X}
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) (hx : ∀ g, a (g,x) = x) :
    x ∈ U ∩ invariantCore a V := by
  exact ⟨hxU,fun g => (hx g).symm ▸ hxV⟩

end QuaternionicSymmetry.CompactActionInvariantNeighborhood
