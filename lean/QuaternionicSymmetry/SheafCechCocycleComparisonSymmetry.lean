import QuaternionicSymmetry.SheafCechCocycleComparison
import Mathlib.Tactic.Abel

namespace QuaternionicSymmetry.SheafCechCocycleComparison

open CategoryTheory TopologicalSpace Opposite SheafCechOneCocycle

variable {B : Type} [TopologicalSpace B] {ι κ : Type*}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)}
  {U : ι → Opens B} {V : κ → Opens B}
  {c : OneCocycle A U} {d : OneCocycle A V}

def Comparison.symm (e : Comparison c d) : Comparison d c where
  value a i W ha hi := -e.value i a W hi ha
  naturality a i W T hTW ha hi := by
    change (restrict A hTW).hom (-e.value i a W hi ha) = _
    rw [map_neg, e.naturality]
  compatibility a b i j W ha hb hi hj := by
    have h := e.compatibility i j a b W hi hj ha hb
    dsimp
    calc
      _ = (e.value i a W hi ha + d.value a b W ha hb) -
          e.value i a W hi ha - e.value j b W hj hb := by abel
      _ = (c.value i j W hi hj + e.value j b W hj hb) -
          e.value i a W hi ha - e.value j b W hj hb := by rw [← h]
      _ = _ := by abel

end QuaternionicSymmetry.SheafCechCocycleComparison
