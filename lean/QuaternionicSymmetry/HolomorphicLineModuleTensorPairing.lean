import QuaternionicSymmetry.HolomorphicLineModuleLocalFree
import QuaternionicSymmetry.HolomorphicLineTensor
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! The genuine bilinear pairing of holomorphic line sections into the
sections of the tensor line. Scalars are holomorphic functions on the
open set. The induced map from the tensor of section modules is not
asserted to be an isomorphism on arbitrary opens: sheafification is needed. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleTensorPairing

open CategoryTheory TopologicalSpace Manifold
open HolomorphicLineModuleSheaf HolomorphicLineModuleLocalFree
open HolomorphicLineTensor HolomorphicLinePowers
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)

theorem coefficient_product (p : ι × κ) {U : Opens B}
    (s : ∀ x : U, Z.Fiber x) (t : ∀ x : U, W.Fiber x) (x : U) :
    coefficient (tensorCore Z W) p (fun y => Mul.mul (α := ℂ) (s y) (t y)) x =
      coefficient Z p.1 s x * coefficient W p.2 t x := by
  change (transitionScalar Z (Z.indexAt x.1) p.1 x.1 *
    transitionScalar W (W.indexAt x.1) p.2 x.1) * (Mul.mul (α := ℂ) (s x) (t x)) = _
  rw [coefficient, coefficient,
    linear_apply_one (Z.coordChange (Z.indexAt x.1) p.1 x.1) (s x),
    linear_apply_one (W.coordChange (W.indexAt x.1) p.2 x.1) (t x)]
  unfold transitionScalar
  exact mul_mul_mul_comm _ _ _ _

/-- Multiplication in the preferred line coordinates, with the actual
tensor transition law, sends holomorphic sections to holomorphic sections. -/
def sectionProduct {U : Opens B}
    (s : sectionSubmodule IB Z U) (t : sectionSubmodule IB W U) :
    sectionSubmodule IB (tensorCore Z W) U := by
  refine ⟨fun x => Mul.mul (α := ℂ) (s.1 x) (t.1 x), ?_⟩
  apply (coefficientPrelocal IB Z).sheafify_inductionOn₂'
    (coefficientPrelocal IB W) (coefficientPrelocal IB (tensorCore Z W))
    (fun a b => Mul.mul (α := ℂ) a b) ?_ s.property t.property
  intro V T a b ha hb p
  have ha' := (coefficientPrelocal IB Z).res (Opens.infLELeft V T) a ha p.1
  have hb' := (coefficientPrelocal IB W).res (Opens.infLERight V T) b hb p.2
  have h : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
      (fun x : (V ⊓ T : Opens B) =>
        coefficient Z p.1 (fun y : (V ⊓ T : Opens B) => a ⟨y.1, y.2.1⟩) x *
        coefficient W p.2 (fun y : (V ⊓ T : Opens B) => b ⟨y.1, y.2.2⟩) x)
      {x | x.1 ∈ Z.baseSet p.1 ∩ W.baseSet p.2} :=
    (ha'.mono (fun _ hx => hx.1)).mul (hb'.mono (fun _ hx => hx.2))
  apply h.congr
  intro x hx
  exact coefficient_product Z W p _ _ x

@[simp] theorem sectionProduct_apply {U : Opens B}
    (s : sectionSubmodule IB Z U) (t : sectionSubmodule IB W U) (x : U) :
    (sectionProduct IB Z W s t).1 x = Mul.mul (α := ℂ) (s.1 x) (t.1 x) := rfl

/-- The actual pairing is bilinear over varying holomorphic scalars. -/
def sectionProductLinear (U : Opens B) :
    sectionSubmodule IB Z U →ₗ[Functions IB U]
      sectionSubmodule IB W U →ₗ[Functions IB U]
        sectionSubmodule IB (tensorCore Z W) U :=
  LinearMap.mk₂ (Functions IB U) (sectionProduct IB Z W)
    (by intro s s' t; apply Subtype.ext; funext x; exact add_mul (R := ℂ) (s.1 x) (s'.1 x) (t.1 x))
    (by
      intro f s t
      apply Subtype.ext
      funext x
      exact @mul_assoc ℂ _ (f x) (s.1 x) (t.1 x))
    (by intro s t t'; apply Subtype.ext; funext x; exact mul_add (R := ℂ) (s.1 x) (t.1 x) (t'.1 x))
    (by
      intro f s t
      apply Subtype.ext
      funext x
      exact @mul_left_comm ℂ _ (s.1 x) (f x) (t.1 x))

/-- The section pairing induces the genuine tensor-product linear map. -/
def tensorMap (U : Opens B) :
    (sectionSubmodule IB Z U ⊗[Functions IB U] sectionSubmodule IB W U) →ₗ[Functions IB U]
      sectionSubmodule IB (tensorCore Z W) U :=
  TensorProduct.lift (sectionProductLinear IB Z W U)

@[simp] theorem tensorMap_tmul (U : Opens B)
    (s : sectionSubmodule IB Z U) (t : sectionSubmodule IB W U) :
    tensorMap IB Z W U (s ⊗ₜ[Functions IB U] t) = sectionProduct IB Z W s t := rfl

theorem sectionProduct_restrict (U V : Opens B) (hVU : V ≤ U)
    (s : sectionSubmodule IB Z U) (t : sectionSubmodule IB W U) :
    (moduleSheaf IB (tensorCore Z W)).val.map (homOfLE hVU).op
        (sectionProduct IB Z W s t) =
      sectionProduct IB Z W
        ((moduleSheaf IB Z).val.map (homOfLE hVU).op s)
        ((moduleSheaf IB W).val.map (homOfLE hVU).op t) := rfl

end
end QuaternionicSymmetry.HolomorphicLineModuleTensorPairing
