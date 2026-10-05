import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Complex.Basic

/-! Actual biholomorphisms preserving a specified complex tangent
distribution in both directions. No algebraicity, finite-dimensional Lie
structure or reductivity is included in this definition. -/

namespace QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphisms

open scoped Manifold ContDiff
noncomputable section

variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace Z] [ChartedSpace V Z] [IsManifold 𝓘(ℂ,V) ∞ Z]
  (D : Z → Submodule ℂ V)

def PreservesForward (f : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) Z Z ∞) : Prop :=
  ∀ z v, v ∈ D z → mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) (f : Z → Z) z v ∈ D (f z)

def Preserves (f : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) Z Z ∞) : Prop :=
  PreservesForward D f ∧ PreservesForward D f.symm

theorem preservesForward_refl :
    PreservesForward D (Diffeomorph.refl 𝓘(ℂ,V) Z ∞) := by
  intro z v hv
  simpa using hv

theorem preservesForward_trans
    {f g : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) Z Z ∞}
    (hf : PreservesForward D f) (hg : PreservesForward D g) :
    PreservesForward D (f.trans g) := by
  intro z v hv
  change mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) ((g : Z → Z) ∘ (f : Z → Z)) z v ∈
    D (g (f z))
  rw [mfderiv_comp z
    (g.contMDiff.mdifferentiable (by simp) (f z))
    (f.contMDiff.mdifferentiable (by simp) z)]
  exact hg (f z) _ (hf z v hv)

theorem preserves_refl : Preserves D (Diffeomorph.refl 𝓘(ℂ,V) Z ∞) :=
  ⟨preservesForward_refl D, preservesForward_refl D⟩

theorem preserves_trans
    {f g : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) Z Z ∞}
    (hf : Preserves D f) (hg : Preserves D g) : Preserves D (f.trans g) := by
  refine ⟨preservesForward_trans D hf.1 hg.1, ?_⟩
  have he : (f.trans g).symm = g.symm.trans f.symm := by
    apply Diffeomorph.ext
    intro z
    rfl
  rw [he]
  exact preservesForward_trans D hg.2 hf.2

theorem preserves_symm {f : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) Z Z ∞}
    (hf : Preserves D f) : Preserves D f.symm :=
  ⟨hf.2, by simpa using hf.1⟩

def Automorphisms :=
  {f : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) Z Z ∞ // Preserves D f}

instance : Group (Automorphisms D) where
  mul f g := ⟨g.1.trans f.1, preserves_trans D g.2 f.2⟩
  one := ⟨Diffeomorph.refl 𝓘(ℂ,V) Z ∞, preserves_refl D⟩
  inv f := ⟨f.1.symm, preserves_symm D f.2⟩
  mul_assoc f g h := by
    apply Subtype.ext
    apply Diffeomorph.ext
    intro z
    rfl
  one_mul f := by
    apply Subtype.ext
    exact Diffeomorph.trans_refl f.1
  mul_one f := by
    apply Subtype.ext
    exact Diffeomorph.refl_trans f.1
  inv_mul_cancel f := by
    apply Subtype.ext
    exact Diffeomorph.self_trans_symm f.1

instance : MulAction (Automorphisms D) Z where
  smul f z := f.1 z
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_eq_apply (f : Automorphisms D) (z : Z) : f • z = f.1 z := rfl

theorem smul_injective : Function.Injective (fun f : Automorphisms D =>
    fun z : Z => f • z) := by
  intro f g h
  apply Subtype.ext
  apply Diffeomorph.ext
  exact congrFun h

end
end QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphisms
