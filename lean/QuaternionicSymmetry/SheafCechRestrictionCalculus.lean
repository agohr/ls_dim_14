import QuaternionicSymmetry.SheafCechOneCocycle

/-! Restriction calculus in the actual abelian sheaf, used to construct
the extension associated with a Čech cocycle. -/

namespace QuaternionicSymmetry.SheafCechOneCocycle

open CategoryTheory TopologicalSpace Opposite

variable {B : Type} [TopologicalSpace B]
  (A : TopCat.Sheaf AddCommGrpCat (TopCat.of B))

theorem restrict_self (V : Opens B) (s : A.val.obj (op V)) :
    restrict A (le_refl V) s = s := by
  have h : restrict A (le_refl V) = 𝟙 (A.val.obj (op V)) := A.val.map_id _
  exact congrArg (fun f : A.val.obj (op V) ⟶ A.val.obj (op V) => f s) h

theorem restrict_restrict {U V W : Opens B} (hWV : W ≤ V) (hVU : V ≤ U)
    (s : A.val.obj (op U)) :
    restrict A hWV (restrict A hVU s) = restrict A (hWV.trans hVU) s := by
  have h : restrict A (hWV.trans hVU) = restrict A hVU ≫ restrict A hWV :=
    A.val.map_comp (homOfLE hVU).op (homOfLE hWV).op
  exact (congrArg (fun f : A.val.obj (op U) ⟶ A.val.obj (op W) => f s) h).symm

end QuaternionicSymmetry.SheafCechOneCocycle
