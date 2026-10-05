import QuaternionicSymmetry.SheafExtensionCocycle

/-! Twisted sections for the cocycle of an extension glue back to
actual sections of its middle sheaf. This is the concrete comparison
needed to recover the original derived extension class. -/

namespace QuaternionicSymmetry.SheafExtensionReconstructionSections

open CategoryTheory TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle SheafShortExactSections
open IntegralSheafLocalUnitLift SheafExtensionCocycle SheafCechTwistedSections
open SheafCechTwistedSectionKernel
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A M : AbelianSheaves B} (f : A ⟶ M) (g : M ⟶ integralSheaf B)
  (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact)
  {U : ι → Opens B} (s : ∀ i, M.val.obj (op (U i)))
  (hs : ∀ i, g.val.app (op (U i)) (s i) = unitSection (U i))

def piece (V : Opens B) (t : SheafCechTwistedSections.sections
    (cocycle f g hfg hS s hs) V) (i : ι) : M.val.obj (op (V ⊓ U i)) :=
  f.val.app (op (V ⊓ U i)) (t.1.2 i) + t.1.1 • restrict M inf_le_right (s i)

theorem piece_restrict (V : Opens B) (t : SheafCechTwistedSections.sections
    (cocycle f g hfg hS s hs) V) (i : ι) {W : Opens B} (hW : W ≤ V ⊓ U i) :
    restrict M hW (piece f g hfg hS s hs V t i) =
      f.val.app (op W) (restrict A hW (t.1.2 i)) +
        t.1.1 • restrict M (hW.trans inf_le_right) (s i) := by
  change (restrict M hW).hom (_ + _ • _) = _
  rw [map_add, map_zsmul, ← map_restrict, restrict_restrict]

theorem pieces_compatible (V : Opens B) (t : SheafCechTwistedSections.sections
    (cocycle f g hfg hS s hs) V) :
    TopCat.Presheaf.IsCompatible M.val (fun i => V ⊓ U i)
      (piece f g hfg hS s hs V t) := by
  intro i j
  let W := (V ⊓ U i) ⊓ (V ⊓ U j)
  let hW : W ≤ overlap (U := U) V i j :=
    le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have heq := congrArg (fun a => restrict A hW a)
    (sections_compat (cocycle f g hfg hS s hs) t i j)
  change (restrict A hW).hom (_ - _) = (restrict A hW).hom (_ • _) at heq
  rw [map_sub, map_zsmul, (cocycle f g hfg hS s hs).naturality,
    restrict_restrict, restrict_restrict] at heq
  have heqf := congrArg (fun a => f.val.app (op W) a) heq
  change (f.val.app (op W)).hom (_ - _) = (f.val.app (op W)).hom (_ • _) at heqf
  rw [map_sub, map_zsmul] at heqf
  change _ - _ = t.1.1 • f.val.app (op W)
    (value f g hfg hS s hs i j W _ _) at heqf
  rw [inclusion_value] at heqf
  dsimp only [difference] at heqf
  rw [smul_sub] at heqf
  change restrict M inf_le_left (piece f g hfg hS s hs V t i) =
    restrict M inf_le_right (piece f g hfg hS s hs V t j)
  rw [piece_restrict, piece_restrict]
  calc
    _ = f.val.app (op W) (restrict A inf_le_left (t.1.2 i)) +
      (t.1.1 • restrict M (inf_le_left.trans inf_le_right) (s i) -
       t.1.1 • restrict M (inf_le_right.trans inf_le_right) (s j)) +
      t.1.1 • restrict M (inf_le_right.trans inf_le_right) (s j) := by abel
    _ = _ := by rw [← heqf]; abel

variable (hcover : ∀ x : B, ∃ i, x ∈ U i)

include hcover in
theorem existsUnique_reconstruction (V : Opens B)
    (t : SheafCechTwistedSections.sections (cocycle f g hfg hS s hs) V) :
    ∃! m : M.val.obj (op V), ∀ i,
      restrict M (show V ⊓ U i ≤ V from inf_le_left) m =
        piece f g hfg hS s hs V t i :=
  TopCat.Sheaf.existsUnique_gluing' M (fun i => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left)
    (pieces_cover hcover V) _ (pieces_compatible f g hfg hS s hs V t)

def reconstruct (V : Opens B)
    (t : SheafCechTwistedSections.sections (cocycle f g hfg hS s hs) V) :
    M.val.obj (op V) :=
  (existsUnique_reconstruction f g hfg hS s hs hcover V t).choose

theorem reconstruct_piece (V : Opens B)
    (t : SheafCechTwistedSections.sections (cocycle f g hfg hS s hs) V) (i : ι) :
    restrict M (show V ⊓ U i ≤ V from inf_le_left)
        (reconstruct f g hfg hS s hs hcover V t) =
      piece f g hfg hS s hs V t i :=
  (existsUnique_reconstruction f g hfg hS s hs hcover V t).choose_spec.1 i

theorem eq_reconstruct (V : Opens B)
    (t : SheafCechTwistedSections.sections (cocycle f g hfg hS s hs) V)
    (m : M.val.obj (op V)) (hm : ∀ i,
      restrict M (show V ⊓ U i ≤ V from inf_le_left) m =
        piece f g hfg hS s hs V t i) :
    m = reconstruct f g hfg hS s hs hcover V t :=
  (existsUnique_reconstruction f g hfg hS s hs hcover V t).choose_spec.2 m hm

end
end QuaternionicSymmetry.SheafExtensionReconstructionSections
