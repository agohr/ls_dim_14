import QuaternionicSymmetry.LocallyConstantCocycleCovering

/-! A section of the actual cocycle covering gives continuous local
gauges with precisely the original Čech coboundary equation. -/

namespace QuaternionicSymmetry.LocallyConstantCocycleGauge

open CategoryTheory TopologicalSpace Opposite
open LocallyConstantRingSheaf SheafCechOneCocycle LocallyConstantCocycleCovering
noncomputable section

variable {B R : Type} {ι : Type*} [TopologicalSpace B] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R]
  {U : ι → Opens B} (c : OneCocycle (sectionSheaf B R) U)
  (indexAt : B → ι) (mem_at : ∀ x : B, x ∈ U (indexAt x))
  (s : C(B, (coveringCore c indexAt mem_at).TotalSpace))
  (hs : ∀ x : B, (s x).proj = x)

def localGauge (i : ι) : C(U i, R) where
  toFun x := ((coveringCore c indexAt mem_at).localTriv i (s x.1)).2
  continuous_toFun := by
    have hc : ContinuousOn
        (fun x : B => ((coveringCore c indexAt mem_at).localTriv i (s x)).2) (U i) := by
      apply ContinuousOn.snd
      apply ((coveringCore c indexAt mem_at).localTriv i).continuousOn.comp
        s.continuous.continuousOn
      intro x hx
      change (s x).proj ∈ U i
      rw [hs]
      exact hx
    exact continuousOn_iff_continuous_restrict.mp hc

theorem localGauge_compat (i j : ι) (x : B) (hi : x ∈ U i) (hj : x ∈ U j) :
    scalar c i j x + localGauge c indexAt mem_at s hs j ⟨x, hj⟩ =
      localGauge c indexAt mem_at s hs i ⟨x, hi⟩ := by
  change scalar c i j x + ((show R from (s x).2) -
      scalar c (indexAt (s x).proj) j (s x).proj) =
    (show R from (s x).2) - scalar c (indexAt (s x).proj) i (s x).proj
  simp only [hs]
  rw [← scalar_comp c (indexAt x) i j x ⟨⟨mem_at x, hi⟩, hj⟩]
  ring

include indexAt mem_at in
theorem exists_gauge [SimplyConnectedSpace B] [LocPathConnectedSpace B]
    [Nonempty B] :
    ∃ a : ∀ i, C(U i, R),
      ∀ i j (x : B) (hi : x ∈ U i) (hj : x ∈ U j),
        scalar c i j x + a j ⟨x, hj⟩ = a i ⟨x, hi⟩ := by
  obtain ⟨s, hs⟩ := exists_continuous_section c indexAt mem_at
  exact ⟨localGauge c indexAt mem_at s hs,
    localGauge_compat c indexAt mem_at s hs⟩

end
end QuaternionicSymmetry.LocallyConstantCocycleGauge
