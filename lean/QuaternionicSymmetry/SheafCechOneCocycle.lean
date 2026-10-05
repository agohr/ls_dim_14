import QuaternionicSymmetry.AbelianSheafCategory

/-! Čech one-cocycles with values in an actual abelian sheaf, written on
every smaller overlap open. Naturality identifies these data with their
values on the full pairwise intersections. This is cocycle data, not a
replacement definition of derived sheaf cohomology. -/

namespace QuaternionicSymmetry.SheafCechOneCocycle

open CategoryTheory TopologicalSpace Opposite
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type*}
  (A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)) (U : ι → Opens B)

abbrev restrict {V W : Opens B} (h : W ≤ V) :
    A.val.obj (op V) ⟶ A.val.obj (op W) := A.val.map (homOfLE h).op

structure OneCocycle where
  value (i j : ι) (V : Opens B) (hi : V ≤ U i) (hj : V ≤ U j) :
    A.val.obj (op V)
  naturality (i j : ι) (V W : Opens B) (hWV : W ≤ V)
      (hi : V ≤ U i) (hj : V ≤ U j) :
    restrict A hWV (value i j V hi hj) =
      value i j W (hWV.trans hi) (hWV.trans hj)
  cocycle (i j k : ι) (V : Opens B)
      (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    value i j V hi hj + value j k V hj hk = value i k V hi hk

variable {A U}

theorem OneCocycle.self (c : OneCocycle A U)
    (i : ι) (V : Opens B) (hi : V ≤ U i) : c.value i i V hi hi = 0 := by
  have h := c.cocycle i i i V hi hi hi
  exact add_left_cancel (h.trans (add_zero _).symm)

theorem OneCocycle.reverse (c : OneCocycle A U)
    (i j : ι) (V : Opens B) (hi : V ≤ U i) (hj : V ≤ U j) :
    c.value j i V hj hi = -c.value i j V hi hj := by
  have h := c.cocycle i j i V hi hj hi
  rw [c.self] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Values on all smaller opens are exactly restrictions of the actual
pairwise-overlap sections; no extra unrelated section data occur. -/
theorem OneCocycle.value_eq_restriction (c : OneCocycle A U)
    (i j : ι) (V : Opens B) (hi : V ≤ U i) (hj : V ≤ U j) :
    c.value i j V hi hj =
      restrict A (le_inf hi hj)
        (c.value i j (U i ⊓ U j) inf_le_left inf_le_right) :=
  (c.naturality i j (U i ⊓ U j) V (le_inf hi hj) inf_le_left inf_le_right).symm

end
end QuaternionicSymmetry.SheafCechOneCocycle
