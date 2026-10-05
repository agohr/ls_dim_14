import QuaternionicSymmetry.SheafCechTwistedSectionMaps
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! The zero-integer twisted sections are exactly genuine global sections
of the original sheaf, proved by its actual gluing axiom. -/

namespace QuaternionicSymmetry.SheafCechTwistedSectionKernel

open CategoryTheory TopologicalSpace Opposite SheafCechOneCocycle
open SheafCechTwistedSections SheafCechTwistedSectionMaps
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)} {U : ι → Opens B}
  (c : OneCocycle A U) (hcover : ∀ x : B, ∃ i, x ∈ U i)

include hcover in
theorem pieces_cover (V : Opens B) : V ≤ ⨆ i, V ⊓ U i := by
  intro x hx
  obtain ⟨i, hi⟩ := hcover x
  exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩

theorem kernel_pieces_compatible (V : Opens B) (s : sections c V)
    (hs : projection c V s = 0) :
    TopCat.Presheaf.IsCompatible A.val (fun i => V ⊓ U i) s.1.2 := by
  intro i j
  let W := (V ⊓ U i) ⊓ (V ⊓ U j)
  have hW : W ≤ overlap (U := U) V i j :=
    le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have heq := sections_compat c s i j
  change s.1.1 = 0 at hs
  rw [hs, zero_zsmul, sub_eq_zero] at heq
  have hres := congrArg (fun a => restrict A hW a) heq
  dsimp only at hres
  rw [restrict_restrict, restrict_restrict] at hres
  exact hres.symm

include hcover in
theorem existsUnique_kernel_section (V : Opens B) (s : sections c V)
    (hs : projection c V s = 0) :
    ∃! a : A.val.obj (op V), inclusion c V a = s := by
  obtain ⟨a, ha, huniq⟩ := A.existsUnique_gluing' (fun i => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (pieces_cover hcover V) s.1.2
    (kernel_pieces_compatible c V s hs)
  refine ⟨a, ?_, ?_⟩
  · apply Subtype.ext
    apply Prod.ext
    · exact hs.symm
    · exact funext ha
  · intro b hb
    apply huniq b
    intro i
    exact congrArg (fun t : sections c V => t.1.2 i) hb

include hcover in
theorem inclusion_injective (V : Opens B) : Function.Injective (inclusion c V) := by
  intro a b hab
  apply A.eq_of_locally_eq' (fun i => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (pieces_cover hcover V) a b
  intro i
  exact congrArg (fun t : sections c V => t.1.2 i) hab

include hcover in
theorem kernel_iff (V : Opens B) (s : sections c V) :
    projection c V s = 0 ↔ ∃ a : A.val.obj (op V), inclusion c V a = s := by
  constructor
  · intro hs
    exact (existsUnique_kernel_section c hcover V s hs).exists
  · rintro ⟨a, rfl⟩
    exact projection_inclusion c V a

end
end QuaternionicSymmetry.SheafCechTwistedSectionKernel
