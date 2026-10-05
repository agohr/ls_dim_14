import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Separation.Hausdorff

/-! A continuous choice between a nonzero vector and its negative has a
locally constant sign. -/
namespace QuaternionicSymmetry.ContinuousSignRigidity
open scoped Topology
variable {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem eventually_eq_of_sign (f g : X → V) (x : X)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hx : g x ≠ 0) (heq : f x = g x)
    (hsign : ∀ᶠ y in 𝓝 x, f y = g y ∨ f y = -g y) : f =ᶠ[𝓝 x] g := by
  have hne : f x ≠ -g x := by
    rw [heq]
    intro h
    have hz : (2 : ℝ) • g x = 0 := by
      simpa only [two_smul] using (eq_neg_iff_add_eq_zero.mp h)
    exact hx ((smul_eq_zero.mp hz).resolve_left two_ne_zero)
  have hn := (hf.ne_iff_eventually_ne hg.neg).mp hne
  filter_upwards [hsign, hn] with y hy hny
  exact hy.resolve_right hny

theorem eventually_eq_or_neg (f g : X → V) (x : X)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hx : g x ≠ 0)
    (hsign : ∀ᶠ y in 𝓝 x, f y = g y ∨ f y = -g y) :
    f =ᶠ[𝓝 x] g ∨ f =ᶠ[𝓝 x] (fun y => -g y) := by
  rcases hsign.self_of_nhds with heq | heq
  · exact Or.inl (eventually_eq_of_sign f g x hf hg hx heq hsign)
  · apply Or.inr
    apply eventually_eq_of_sign f (fun y => -g y) x hf hg.neg (neg_ne_zero.mpr hx) heq
    filter_upwards [hsign] with y hy
    simpa only [neg_neg, or_comm] using hy

end QuaternionicSymmetry.ContinuousSignRigidity
