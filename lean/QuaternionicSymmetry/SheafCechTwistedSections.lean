import QuaternionicSymmetry.SheafCechRestrictionCalculus
import Mathlib.Tactic.Abel

/-! The actual abelian groups of twisted sections used to construct the
extension attached to a Čech cocycle. A section consists of an integer n
and local sections whose differences are n times the supplied cocycle.
The integer is constant at the presheaf level; sheafification will supply
locally constant integers. No derived-H¹ identification is asserted here. -/

namespace QuaternionicSymmetry.SheafCechTwistedSections

open CategoryTheory TopologicalSpace Opposite SheafCechOneCocycle
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)} {U : ι → Opens B}
  (c : OneCocycle A U)

abbrev overlap (V : Opens B) (i j : ι) : Opens B := (V ⊓ U i) ⊓ U j

abbrev rawSections (V : Opens B) := ℤ × ∀ i : ι, A.val.obj (op (V ⊓ U i))

def twistedSubgroup (V : Opens B) : AddSubgroup (rawSections (A := A) (U := U) V) where
  carrier := {s | ∀ i j : ι,
    restrict A (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (s.2 j) - restrict A inf_le_left (s.2 i) =
      s.1 • c.value i j (overlap (U := U) V i j)
        (inf_le_left.trans inf_le_right) inf_le_right}
  zero_mem' := by
    intro i j
    change (restrict A _).hom 0 - (restrict A _).hom 0 = (0 : ℤ) • _
    simp
  add_mem' := by
    intro s t hs ht i j
    change (restrict A _).hom (s.2 j + t.2 j) -
      (restrict A _).hom (s.2 i + t.2 i) = (s.1 + t.1) • _
    rw [map_add, map_add, add_zsmul]
    calc
      _ = (restrict A _ (s.2 j) - restrict A _ (s.2 i)) +
          (restrict A _ (t.2 j) - restrict A _ (t.2 i)) := by abel
      _ = _ := congrArg₂ (fun x y => x + y) (hs i j) (ht i j)
  neg_mem' := by
    intro s hs i j
    change (restrict A _).hom (-s.2 j) -
      (restrict A _).hom (-s.2 i) = (-s.1) • _
    rw [map_neg, map_neg, neg_zsmul]
    calc
      _ = -(restrict A _ (s.2 j) - restrict A _ (s.2 i)) := by abel
      _ = _ := congrArg Neg.neg (hs i j)

abbrev sections (V : Opens B) := twistedSubgroup c V

theorem sections_compat {V : Opens B} (s : sections c V) (i j : ι) :
    restrict A (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (s.1.2 j) - restrict A inf_le_left (s.1.2 i) =
      s.1.1 • c.value i j (overlap (U := U) V i j)
        (inf_le_left.trans inf_le_right) inf_le_right := s.2 i j

/-- Restriction retains the integer and restricts the actual local
sections. Its compatibility is the naturality of the given cocycle. -/
def restriction {V W : Opens B} (hWV : W ≤ V) : sections c V →+ sections c W where
  toFun s := ⟨⟨s.1.1, fun i => restrict A (inf_le_inf_right (U i) hWV) (s.1.2 i)⟩, by
    intro i j
    let h : overlap (U := U) W i j ≤ overlap (U := U) V i j :=
      inf_le_inf_right (U j) (inf_le_inf_right (U i) hWV)
    have heq := congrArg (fun a => restrict A h a) (sections_compat c s i j)
    change (restrict A h).hom (_ - _) = (restrict A h).hom (_ • _) at heq
    rw [map_sub, map_zsmul, c.naturality] at heq
    change restrict A h (restrict A _ (s.1.2 j)) -
      restrict A h (restrict A _ (s.1.2 i)) = _ at heq
    rw [restrict_restrict, restrict_restrict] at heq
    change restrict A _ (restrict A _ (s.1.2 j)) -
      restrict A _ (restrict A _ (s.1.2 i)) = _
    rw [restrict_restrict, restrict_restrict]
    exact heq⟩
  map_zero' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact map_zero (restrict A _).hom
  map_add' s t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact map_add (restrict A _).hom _ _

theorem restriction_self (V : Opens B) (s : sections c V) :
    restriction c (le_refl V) s = s := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i
    exact restrict_self A _ _

theorem restriction_comp {T V W : Opens B} (hWV : W ≤ V) (hVT : V ≤ T)
    (s : sections c T) :
    restriction c hWV (restriction c hVT s) = restriction c (hWV.trans hVT) s := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i
    exact restrict_restrict A _ _ _

def twistedPresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of B) where
  obj V := AddCommGrpCat.of (sections c V.unop)
  map f := AddCommGrpCat.ofHom (restriction c f.unop.le)
  map_id V := by
    apply AddCommGrpCat.ext
    intro s
    exact restriction_self c V.unop s
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro s
    exact (restriction_comp c g.unop.le f.unop.le s).symm

end
end QuaternionicSymmetry.SheafCechTwistedSections
