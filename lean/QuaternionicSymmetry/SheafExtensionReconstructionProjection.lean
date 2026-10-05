import QuaternionicSymmetry.SheafExtensionReconstructionNatural

/-! Reconstruction preserves the actual quotient map to the constant
integral sheaf. The integer presheaf maps through its canonical sheafification
unit, rather than being identified with all locally constant sections. -/

namespace QuaternionicSymmetry.SheafExtensionReconstructionProjection

open CategoryTheory TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle SheafShortExactSections
open IntegralSheafLocalUnitLift SheafExtensionCocycle SheafCechTwistedSections
open SheafCechTwistedSectionMaps SheafCechTwistedPresheafSequence
open SheafCechTwistedSectionKernel
open SheafExtensionReconstructionSections SheafExtensionReconstructionNatural
noncomputable section

variable {B : Type} [TopologicalSpace B]

theorem integerSection_eq_zsmul_unit (V : Opens B) (n : ℤ) :
    (toSheafify (Opens.grothendieckTopology (TopCat.of B))
      (constantIntegerPresheaf (B := B))).app (op V) (ULift.up n) =
      n • unitSection V := by
  have hn : (ULift.up n : ULift.{0} ℤ) = n • (ULift.up 1 : ULift.{0} ℤ) := by
    apply ULift.ext
    change n = n • (1 : ℤ)
    simp
  rw [hn]
  exact map_zsmul ((toSheafify (Opens.grothendieckTopology (TopCat.of B))
    (constantIntegerPresheaf (B := B))).app (op V)).hom _ _

variable {ι : Type} {A M : AbelianSheaves B}
  (f : A ⟶ M) (g : M ⟶ integralSheaf B)
  (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact)
  {U : ι → Opens B} (s : ∀ i, M.val.obj (op (U i)))
  (hs : ∀ i, g.val.app (op (U i)) (s i) = unitSection (U i))

theorem piece_projection (V : Opens B)
    (t : SheafCechTwistedSections.sections (cocycle f g hfg hS s hs) V) (i : ι) :
    g.val.app (op (V ⊓ U i)) (piece f g hfg hS s hs V t i) =
      t.1.1 • unitSection (V ⊓ U i) := by
  have hzero := ((ShortComplex.mk f g hfg).map
    (SheafShortExactSections.sections (V ⊓ U i))).ab_zero_apply (t.1.2 i)
  change (g.val.app (op (V ⊓ U i))).hom (_ + _ • _) = _
  rw [map_add, map_zsmul, map_restrict, hs, unitSection_restrict]
  change g.val.app (op (V ⊓ U i)) (f.val.app (op (V ⊓ U i)) (t.1.2 i)) = 0 at hzero
  rw [hzero, zero_add]

variable (hcover : ∀ x : B, ∃ i, x ∈ U i)

theorem reconstruct_projection (V : Opens B)
    (t : SheafCechTwistedSections.sections (cocycle f g hfg hS s hs) V) :
    g.val.app (op V) (reconstruct f g hfg hS s hs hcover V t) =
      t.1.1 • unitSection V := by
  apply TopCat.Sheaf.eq_of_locally_eq' (integralSheaf B)
    (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left) (pieces_cover hcover V)
  intro i
  rw [← map_restrict, reconstruct_piece]
  change _ = (restrict (integralSheaf B) inf_le_left).hom (_ • _)
  rw [map_zsmul, unitSection_restrict]
  exact piece_projection f g hfg hS s hs V t i

theorem reconstructionNat_projection :
    reconstructionNat f g hfg hS s hs hcover ≫ g.val =
      projectionNat (cocycle f g hfg hS s hs) ≫
        toSheafify (Opens.grothendieckTopology (TopCat.of B))
          (constantIntegerPresheaf (B := B)) := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro t
  exact (reconstruct_projection f g hfg hS s hs hcover V.unop t).trans
    (integerSection_eq_zsmul_unit V.unop t.1.1).symm

end
end QuaternionicSymmetry.SheafExtensionReconstructionProjection
