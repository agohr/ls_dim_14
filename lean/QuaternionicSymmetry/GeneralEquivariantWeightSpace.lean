import QuaternionicSymmetry.ManifoldQuaternionicTorusAction
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Weight submodules for a family of actual linear operators, and their
transport across an intertwining linear equivalence. No representation
or character existence is assumed. -/

namespace QuaternionicSymmetry.GeneralEquivariantWeightSpace

noncomputable section

variable {T V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def weightSubmodule (ρ : T → V →ₗ[ℂ] V) (χ : T → ℂ) : Submodule ℂ V where
  carrier := {v | ∀ t, ρ t v = χ t • v}
  zero_mem' := by
    intro t
    simp
  add_mem' := by
    intro x y hx hy t
    rw [map_add, hx t, hy t, smul_add]
  smul_mem' := by
    intro c x hx t
    rw [map_smul, hx t, smul_comm]

theorem mem_weightSubmodule_iff (ρ : T → V →ₗ[ℂ] V) (χ : T → ℂ)
    (v : V) : v ∈ weightSubmodule ρ χ ↔ ∀ t, ρ t v = χ t • v := Iff.rfl

def weightSubmoduleEquiv (ρ : T → V →ₗ[ℂ] V)
    (σ : T → W →ₗ[ℂ] W) (χ : T → ℂ)
    (F : V ≃ₗ[ℂ] W)
    (h : ∀ t v, F (ρ t v) = σ t (F v)) :
    weightSubmodule ρ χ ≃ₗ[ℂ] weightSubmodule σ χ where
  toFun v := ⟨F v, by
    intro t
    have hv := v.2 t
    have ht := h t v
    rw [hv, map_smul] at ht
    exact ht.symm⟩
  invFun w := ⟨F.symm w, by
    intro t
    apply F.injective
    rw [h t, map_smul]
    simp only [LinearEquiv.apply_symm_apply]
    exact w.2 t⟩
  left_inv := by
    intro v
    apply Subtype.ext
    exact F.symm_apply_apply v
  right_inv := by
    intro w
    apply Subtype.ext
    exact F.apply_symm_apply w
  map_add' := by
    intro x y
    apply Subtype.ext
    exact map_add F (x : V) (y : V)
  map_smul' := by
    intro c x
    apply Subtype.ext
    exact map_smul F c (x : V)

theorem finrank_weightSubmodule_eq
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : T → V →ₗ[ℂ] V) (σ : T → W →ₗ[ℂ] W) (χ : T → ℂ)
    (F : V ≃ₗ[ℂ] W) (h : ∀ t v, F (ρ t v) = σ t (F v)) :
    Module.finrank ℂ (weightSubmodule ρ χ) =
      Module.finrank ℂ (weightSubmodule σ χ) :=
  (weightSubmoduleEquiv ρ σ χ F h).finrank_eq

end
end QuaternionicSymmetry.GeneralEquivariantWeightSpace
