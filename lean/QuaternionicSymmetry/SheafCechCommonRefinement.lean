import QuaternionicSymmetry.SheafCechCohomologyRefinement

/-! Actual common-refinement coboundary comparisons on arbitrary covers
preserve the constructed class in Mathlib's derived H¹. -/

namespace QuaternionicSymmetry.SheafCechCommonRefinement

open CategoryTheory TopologicalSpace Opposite
open SheafCechOneCocycle SheafCechCocycleComparison SheafCechRefinement
open SheafCechExtension SheafCechCohomologyRefinement
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι κ : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)}
  {U : ι → Opens B} {V : κ → Opens B}
  {c : OneCocycle A U} {d : OneCocycle A V}

def commonCover (U : ι → Opens B) (V : κ → Opens B) (p : ι × κ) : Opens B :=
  U p.1 ⊓ V p.2

theorem commonCover_covers
    (hU : ∀ x : B, ∃ i, x ∈ U i) (hV : ∀ x : B, ∃ a, x ∈ V a) :
    ∀ x : B, ∃ p, x ∈ commonCover U V p := by
  intro x
  obtain ⟨i, hi⟩ := hU x
  obtain ⟨a, ha⟩ := hV x
  exact ⟨(i, a), hi, ha⟩

def commonComparison (e : Comparison c d) :
    Comparison
      (refinedCocycle c (V := commonCover U V) Prod.fst (fun _ => inf_le_left))
      (refinedCocycle d (V := commonCover U V) Prod.snd (fun _ => inf_le_right)) where
  value p q T hp hq := e.value p.1 q.2 T (hp.trans inf_le_left) (hq.trans inf_le_right)
  naturality p q T W hWT hp hq := e.naturality p.1 q.2 T W hWT _ _
  compatibility p q a b T hp hq ha hb :=
    e.compatibility p.1 q.1 a.2 b.2 T _ _ _ _

/-- The comparison on arbitrary charts gives equality of genuine derived
classes via the actual common cover, not a new quotient definition. -/
theorem cohomologyClass_comparison (e : Comparison c d)
    (hU : ∀ x : B, ∃ i, x ∈ U i) (hV : ∀ x : B, ∃ a, x ∈ V a) :
    cohomologyClass c hU = cohomologyClass d hV := by
  have hW := commonCover_covers hU hV
  calc
    cohomologyClass c hU =
        cohomologyClass (refinedCocycle c (V := commonCover U V)
          Prod.fst (fun _ => inf_le_left)) hW :=
      cohomologyClass_refinement c Prod.fst (fun _ => inf_le_left) hU hW
    _ = cohomologyClass (refinedCocycle d (V := commonCover U V)
          Prod.snd (fun _ => inf_le_right)) hW :=
      SheafCechCohomologyComparison.cohomologyClass_eq (commonComparison e) hW
    _ = cohomologyClass d hV :=
      (cohomologyClass_refinement d Prod.snd (fun _ => inf_le_right) hV hW).symm

end
end QuaternionicSymmetry.SheafCechCommonRefinement
