import QuaternionicSymmetry.CompactLieTorusInputs
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! A continuous surjective real-coordinate homomorphism whose kernel is a
full lattice gives a literal circle-power torus presentation. -/
namespace QuaternionicSymmetry.FullLatticeCirclePresentation
open Module Function CompactLieTorusInputs
noncomputable section
variable {d : ℕ} (L : Submodule ℤ (Fin d → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]

def realBasis : Basis (Fin d) ℝ (Fin d → ℝ) :=
  (IsZLattice.basis L).ofZLatticeBasis ℝ L

def characters : Multiplicative (Fin d → ℝ) →* (Fin d → Circle) where
  toFun x i := Circle.exp (2 * Real.pi * (realBasis L).equivFun (Multiplicative.toAdd x) i)
  map_one' := by funext i; simp
  map_mul' x y := by
    funext i
    change Circle.exp (2 * Real.pi * ((realBasis L).equivFun
      (Multiplicative.toAdd x + Multiplicative.toAdd y) i)) = _
    rw [map_add, Pi.add_apply, mul_add, Circle.exp_add]
    rfl

theorem characters_continuous : Continuous (characters L) := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp (continuous_const.mul
    ((continuous_apply i).comp ((realBasis L).equivFun.toLinearMap.continuous_of_finiteDimensional.comp continuous_toAdd)))

theorem characters_surjective : Surjective (characters L) := by
  intro t
  refine ⟨Multiplicative.ofAdd ((realBasis L).equivFun.symm
    (fun i => Complex.arg (t i) / (2 * Real.pi))),?_⟩
  funext i
  change Circle.exp (2 * Real.pi *
    ((realBasis L).equivFun ((realBasis L).equivFun.symm _) i)) = t i
  rw [LinearEquiv.apply_symm_apply]
  rw [mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))]
  exact Circle.exp_arg _

theorem characters_eq_one (x : Fin d → ℝ) :
    characters L (Multiplicative.ofAdd x) = 1 ↔ x ∈ L := by
  have hspan : Submodule.span ℤ (Set.range (realBasis L)) = L :=
    (IsZLattice.basis L).ofZLatticeBasis_span ℝ
  conv_rhs => rw [← hspan, (realBasis L).mem_span_iff_repr_mem ℤ x]
  constructor
  · intro h i
    have hi := congrFun h i
    change Circle.exp (2 * Real.pi * ((realBasis L).equivFun x i)) = 1 at hi
    obtain ⟨n,hn⟩ := Circle.exp_eq_one.mp hi
    refine ⟨n,?_⟩
    change (n : ℝ) = (realBasis L).equivFun x i
    nlinarith [Real.pi_pos]
  · intro h
    funext i
    obtain ⟨n,hn⟩ := h i
    change Circle.exp (2 * Real.pi * ((realBasis L).repr x i)) = 1
    rw [← hn]
    exact Circle.exp_two_pi_mul_int n

variable {G : Type} [Group G] [TopologicalSpace G]
  (f : Multiplicative (Fin d → ℝ) →* G)
  (hf : Continuous f) (hs : Surjective f)
  (hk : ∀ x : Fin d → ℝ, f (Multiplicative.ofAdd x) = 1 ↔ x ∈ L)

include L f hf hs hk in
theorem exists_torus_presentation :
    ∃ T : TorusEmbedding G d, Surjective T.hom := by
  have hker : (characters L).ker ≤ f.ker := by
    intro x hx
    exact (hk (Multiplicative.toAdd x)).mpr ((characters_eq_one L _).mp hx)
  let q := (characters L).liftOfSurjective (characters_surjective L) ⟨f,hker⟩
  have hcomp (x) : q (characters L x) = f x := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hqc : Continuous q := by
    have ho := (characters L).isOpenMap_of_sigmaCompact
      (characters_surjective L) (characters_continuous L)
    apply (ho.isQuotientMap (characters_continuous L) (characters_surjective L)).continuous_iff.mpr
    have he : q ∘ characters L = f := funext hcomp
    rwa [he]
  have hqi : Injective q := by
    intro x y hxy
    obtain ⟨a,rfl⟩ := characters_surjective L x
    obtain ⟨b,rfl⟩ := characters_surjective L y
    apply div_eq_one.mp
    rw [← map_div]
    apply (characters_eq_one L _).mpr
    apply (hk _).mp
    change f (a/b) = 1
    rw [map_div, ← hcomp a, ← hcomp b, hxy, div_self']
  refine ⟨⟨q,hqc,hqi⟩,?_⟩
  intro y
  obtain ⟨x,hx⟩ := hs y
  exact ⟨characters L x,(hcomp x).trans hx⟩

end
end QuaternionicSymmetry.FullLatticeCirclePresentation
