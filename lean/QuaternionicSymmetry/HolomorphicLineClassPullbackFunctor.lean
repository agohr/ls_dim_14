import QuaternionicSymmetry.HolomorphicLineClassPullback
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Identity, composition, and biholomorphic invariance of the actual
line-bundle class group. These use literal holomorphic bundle pullbacks;
they do not substitute an abstract group for the geometric classes. -/

namespace QuaternionicSymmetry.HolomorphicLineClassPullbackFunctor

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineClassPullback
open scoped Manifold ContDiff
noncomputable section

universe u
variable {B B' B'' H H' H'' F F' F'' : Type*}
  [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace B'']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [NormedAddCommGroup F''] [NormedSpace ℂ F'']
  [ChartedSpace H B] [ChartedSpace H' B'] [ChartedSpace H'' B'']
  (IB : ModelWithCorners ℂ F H)
  (IB' : ModelWithCorners ℂ F' H')
  (IB'' : ModelWithCorners ℂ F'' H'')

@[simp] theorem pullbackHom_id (c : CoreClass.{u} (B := B) IB) :
    pullbackHom IB IB id contMDiff_id c = c := by
  induction c using Quotient.inductionOn with
  | h L => rfl

theorem pullbackHom_comp
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f)
    (g : B'' → B') (hg : ContMDiff IB'' IB' ∞ g)
    (c : CoreClass.{u} (B := B) IB) :
    pullbackHom IB' IB'' g hg (pullbackHom IB IB' f hf c) =
      pullbackHom IB IB'' (f ∘ g) (hf.comp hg) c := by
  induction c using Quotient.inductionOn with
  | h L => rfl

theorem pullbackHom_congr
    (f g : B' → B) (hf : ContMDiff IB' IB ∞ f)
    (hg : ContMDiff IB' IB ∞ g) (hfg : f = g) :
    pullbackHom.{u} IB IB' f hf = pullbackHom.{u} IB IB' g hg := by
  subst g
  rfl

/-- An actual biholomorphism induces a group equivalence of genuine
holomorphic line-bundle isomorphism classes, contravariantly. -/
def pullbackEquiv (e : Diffeomorph IB' IB B' B ∞) :
    CoreClass.{u} (B := B) IB ≃* CoreClass.{u} (B := B') IB' where
  toFun := pullbackHom IB IB' e e.contMDiff
  invFun := pullbackHom IB' IB e.symm e.symm.contMDiff
  left_inv c := by
    rw [pullbackHom_comp]
    have he : (e : B' → B) ∘ (e.symm : B → B') = id := by
      funext x
      exact e.apply_symm_apply x
    rw [pullbackHom_congr IB IB _ id _ contMDiff_id he, pullbackHom_id]
  right_inv c := by
    rw [pullbackHom_comp]
    have he : (e.symm : B → B') ∘ (e : B' → B) = id := by
      funext x
      exact e.symm_apply_apply x
    rw [pullbackHom_congr IB' IB' _ id _ contMDiff_id he, pullbackHom_id]
  map_mul' := (pullbackHom IB IB' e e.contMDiff).map_mul

end
end QuaternionicSymmetry.HolomorphicLineClassPullbackFunctor
