import QuaternionicSymmetry.SheafExtensionReconstructionSections

/-! The genuine gluing reconstruction is additive and natural in the
open set, giving a morphism from the twisted presheaf to the original
middle sheaf, compatible with its coefficient inclusion. -/

namespace QuaternionicSymmetry.SheafExtensionReconstructionNatural

open CategoryTheory TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle SheafShortExactSections
open IntegralSheafLocalUnitLift SheafExtensionCocycle SheafCechTwistedSections
open SheafCechTwistedSectionMaps SheafCechTwistedPresheafSequence
open SheafExtensionReconstructionSections
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A M : AbelianSheaves B} (f : A ⟶ M) (g : M ⟶ integralSheaf B)
  (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact)
  {U : ι → Opens B} (s : ∀ i, M.val.obj (op (U i)))
  (hs : ∀ i, g.val.app (op (U i)) (s i) = unitSection (U i))
  (hcover : ∀ x : B, ∃ i, x ∈ U i)

theorem reconstruct_zero (V : Opens B) :
    reconstruct f g hfg hS s hs hcover V 0 = 0 := by
  symm
  apply eq_reconstruct
  intro i
  change (restrict M _).hom 0 = (f.val.app (op (V ⊓ U i))).hom 0 + (0 : ℤ) • _
  simp only [map_zero, zero_zsmul, add_zero]

theorem reconstruct_add (V : Opens B)
    (u v : SheafCechTwistedSections.sections (cocycle f g hfg hS s hs) V) :
    reconstruct f g hfg hS s hs hcover V (u + v) =
      reconstruct f g hfg hS s hs hcover V u +
        reconstruct f g hfg hS s hs hcover V v := by
  symm
  apply eq_reconstruct
  intro i
  change (restrict M _).hom (_ + _) = _
  rw [map_add, reconstruct_piece, reconstruct_piece]
  change (f.val.app (op (V ⊓ U i))).hom (u.1.2 i) + u.1.1 • _ +
      ((f.val.app (op (V ⊓ U i))).hom (v.1.2 i) + v.1.1 • _) =
    (f.val.app (op (V ⊓ U i))).hom (u.1.2 i + v.1.2 i) + (u.1.1 + v.1.1) • _
  rw [map_add, add_zsmul]
  abel

theorem reconstruct_restrict {V W : Opens B} (hWV : W ≤ V)
    (t : SheafCechTwistedSections.sections (cocycle f g hfg hS s hs) V) :
    restrict M hWV (reconstruct f g hfg hS s hs hcover V t) =
      reconstruct f g hfg hS s hs hcover W
        (restriction (cocycle f g hfg hS s hs) hWV t) := by
  apply eq_reconstruct
  intro i
  have h := congrArg (fun m => restrict M (inf_le_inf_right (U i) hWV) m)
    (reconstruct_piece f g hfg hS s hs hcover V t i)
  dsimp only at h
  rw [restrict_restrict, piece_restrict] at h
  rw [restrict_restrict]
  exact h

theorem reconstruct_inclusion (V : Opens B) (a : A.val.obj (op V)) :
    reconstruct f g hfg hS s hs hcover V
        (inclusion (cocycle f g hfg hS s hs) V a) = f.val.app (op V) a := by
  symm
  apply eq_reconstruct
  intro i
  rw [← map_restrict]
  change _ = f.val.app (op (V ⊓ U i)) (restrict A inf_le_left a) + (0 : ℤ) • _
  rw [zero_zsmul, add_zero]

def reconstructionNat : twistedPresheaf (cocycle f g hfg hS s hs) ⟶ M.val where
  app V := AddCommGrpCat.ofHom {
    toFun := reconstruct f g hfg hS s hs hcover V.unop
    map_zero' := reconstruct_zero f g hfg hS s hs hcover V.unop
    map_add' := reconstruct_add f g hfg hS s hs hcover V.unop }
  naturality V W k := by
    apply AddCommGrpCat.ext
    intro t
    exact (reconstruct_restrict f g hfg hS s hs hcover k.unop.le t).symm

theorem inclusionNat_reconstructionNat :
    inclusionNat (cocycle f g hfg hS s hs) ≫
      reconstructionNat f g hfg hS s hs hcover = f.val := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro a
  exact reconstruct_inclusion f g hfg hS s hs hcover V.unop a

end
end QuaternionicSymmetry.SheafExtensionReconstructionNatural
