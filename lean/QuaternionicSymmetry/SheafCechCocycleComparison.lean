import QuaternionicSymmetry.SheafCechOneCocycle

/-! A change of Čech cocycle on arbitrary covers, expressed by actual
sheaf sections on the common refinement and the genuine coboundary law. -/

namespace QuaternionicSymmetry.SheafCechCocycleComparison

open CategoryTheory TopologicalSpace Opposite SheafCechOneCocycle

variable {B : Type} [TopologicalSpace B] {ι κ : Type*}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)}
  {U : ι → Opens B} {V : κ → Opens B}

/-- Refinement-independent coboundary data. Values are sections on the
actual common opens, with their restriction naturality included. -/
structure Comparison (c : OneCocycle A U) (d : OneCocycle A V) where
  value (i : ι) (a : κ) (W : Opens B) (hi : W ≤ U i) (ha : W ≤ V a) :
    A.val.obj (op W)
  naturality (i : ι) (a : κ) (W T : Opens B) (hTW : T ≤ W)
      (hi : W ≤ U i) (ha : W ≤ V a) :
    restrict A hTW (value i a W hi ha) =
      value i a T (hTW.trans hi) (hTW.trans ha)
  compatibility (i j : ι) (a b : κ) (W : Opens B)
      (hi : W ≤ U i) (hj : W ≤ U j) (ha : W ≤ V a) (hb : W ≤ V b) :
    c.value i j W hi hj + value j b W hj hb =
      value i a W hi ha + d.value a b W ha hb

end QuaternionicSymmetry.SheafCechCocycleComparison
