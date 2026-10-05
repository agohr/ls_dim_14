import QuaternionicSymmetry.ManifoldDeRhamWedge
import QuaternionicSymmetry.ContinuousWedgeAssocComparison
import QuaternionicSymmetry.ContinuousWedgeGradedSwap

/-!
Positive-degree de Rham algebra laws on genuine manifold tangent forms.
Degree zero and a unit belong to a later stage.
-/

namespace QuaternionicSymmetry.ManifoldDeRhamRing

open QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldDeRhamWedge
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 500000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Exact smooth forms as a real subspace of closed smooth forms. -/
noncomputable def exactClosedSubmodule (k : ℕ) :
    Submodule ℝ (closedForms (E := E) (M₀ := M) (k + 1)) where
  carrier := {α | (α.1 :
    smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := k + 1)) ∈
      exactForms (E := E) (M₀ := M) k}
  zero_mem' := (exactForms (E := E) (M₀ := M) k).zero_mem
  add_mem' := by
    intro α β hα hβ
    exact (exactForms (E := E) (M₀ := M) k).add_mem hα hβ
  smul_mem' := by
    intro c α hα
    exact (exactForms (E := E) (M₀ := M) k).smul_mem c hα

theorem exactClosedSubmodule_toAddSubgroup (k : ℕ) :
    (exactClosedSubmodule (E := E) (M := M) k).toAddSubgroup =
      exactClosedAddSubgroup (E := E) (M₀ := M) k := by
  rfl

/-- The quotient scalar action is the one induced from closed forms. -/
noncomputable instance positiveDegreeCohomologySMul (k : ℕ) :
    SMul ℝ (positiveDegreeCohomology (E := E) (M₀ := M) k) :=
  ⟨cohomologyScalar (E := E) (M := M) k⟩

/-- The form-to-class map is an additive homomorphism. -/
noncomputable def closedFormClassHom (k : ℕ) :
    (closedForms (E := E) (M₀ := M) (k + 1)) →+
      positiveDegreeCohomology (E := E) (M₀ := M) k where
  toFun := closedFormClass k
  map_zero' := rfl
  map_add' α β := QuotientAddGroup.mk_add
    (exactClosedAddSubgroup (E := E) (M₀ := M) k) α β

theorem closedFormClassHom_surjective (k : ℕ) :
    Function.Surjective (closedFormClassHom (E := E) (M := M) k) := by
  intro a
  refine QuotientAddGroup.induction_on a ?_
  intro α
  exact ⟨α, rfl⟩

/-- The standard real module laws descend from closed forms through the
surjective form-to-class additive map. -/
noncomputable instance positiveDegreeCohomologyModule (k : ℕ) :
    Module ℝ (positiveDegreeCohomology (E := E) (M₀ := M) k) :=
  Function.Surjective.module ℝ
    (closedFormClassHom (E := E) (M := M) k)
    (closedFormClassHom_surjective (E := E) (M := M) k)
    (by intro c α; rfl)

theorem cohomologyScalar_eq_smul (k : ℕ) (c : ℝ)
    (a : positiveDegreeCohomology (E := E) (M₀ := M) k) :
    cohomologyScalar k c a = c • a := rfl

private noncomputable instance tangentNormedGroup (x : M) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := by
  change NormedAddCommGroup E
  infer_instance

private noncomputable instance tangentNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := by
  change NormedSpace ℝ E
  infer_instance

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem castForm_apply {m n : ℕ} (h : m = n)
    (α : Form 𝓘(ℝ, E) M m) (x : M)
    (v : Fin n → TangentSpace 𝓘(ℝ, E) x) :
    castForm h α x v = α x (v ∘ finCongr h) := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem formWedge_cast_left {p p' q : ℕ} (h : p = p')
    (α : Form 𝓘(ℝ, E) M p)
    (β : Form 𝓘(ℝ, E) M q) :
    formWedge (castForm h α) β =
      castForm (congrArg (· + q) h) (formWedge α β) := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem formWedge_cast_right {p q q' : ℕ} (h : q = q')
    (α : Form 𝓘(ℝ, E) M p)
    (β : Form 𝓘(ℝ, E) M q) :
    formWedge α (castForm h β) =
      castForm (congrArg (p + ·) h) (formWedge α β) := by
  cases h
  rfl

/-- Transport a closed form along an equality of positive-degree indices. -/
noncomputable def castClosed {a b : ℕ} (h : a = b)
    (α : closedForms (E := E) (M₀ := M) (a + 1)) :
    closedForms (E := E) (M₀ := M) (b + 1) := by
  cases h
  exact α

theorem castClosed_form {a b : ℕ} (h : a = b)
    (α : closedForms (E := E) (M₀ := M) (a + 1)) :
    (castClosed h α).1.1 =
      castForm (congrArg Nat.succ h) α.1.1 := by
  cases h
  rfl

/-- Transport a positive-degree class along an equality of degree indices. -/
noncomputable def castClass {a b : ℕ} (h : a = b)
    (z : positiveDegreeCohomology (E := E) (M₀ := M) a) :
    positiveDegreeCohomology (E := E) (M₀ := M) b := by
  cases h
  exact z

theorem castClass_mk {a b : ℕ} (h : a = b)
    (α : closedForms (E := E) (M₀ := M) (a + 1)) :
    castClass h (QuotientAddGroup.mk α) =
      QuotientAddGroup.mk (castClosed h α) := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Associativity of the global normalized wedge, including the canonical
reassociation of tangent argument indices. -/
theorem formWedge_assoc {p q r : ℕ}
    (α : Form 𝓘(ℝ, E) M p)
    (β : Form 𝓘(ℝ, E) M q)
    (γ : Form 𝓘(ℝ, E) M r) :
    castForm (Nat.add_assoc p q r)
      (formWedge (formWedge α β) γ) =
        formWedge α (formWedge β γ) := by
  funext x
  ext v
  rw [castForm_apply]
  change ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ) (α x) (β x))
    (γ x) (v ∘ finCongr (Nat.add_assoc p q r)) =
    ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ) (α x)
      (ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ) (β x) (γ x)) v
  have h := ContinuousWedgeAssocComparison.wedge_assoc_apply
    (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ)
    (by intro a b c; exact mul_assoc a b c)
    (α x) (β x) (γ x) (v ∘ finCongr (Nat.add_assoc p q r))
  simpa only [Function.comp_assoc, Equiv.apply_symm_apply,
    Function.comp_apply] using h

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formWedge_swap {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (α : Form 𝓘(ℝ, E) M p)
    (β : Form 𝓘(ℝ, E) M q) :
    castForm (Nat.add_comm q p) (formWedge β α) =
      (-1 : ℝ) ^ (p * q) • formWedge α β := by
  funext x
  ext v
  rw [castForm_apply]
  change ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ) (β x) (α x)
      (v ∘ finCongr (Nat.add_comm q p)) =
    (-1 : ℝ) ^ (p * q) •
      ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ) (α x) (β x) v
  exact ContinuousWedgeGradedSwap.wedge_swap hp hq (α x) (β x) v

theorem closedWedge_assoc (k l m : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1))
    (γ : closedForms (E := E) (M₀ := M) (m + 1)) :
    castClosed
      (show (k + l + 1) + m + 1 = k + (l + m + 1) + 1 by omega)
      (closedWedge (k + l + 1) m (closedWedge k l α β) γ) =
        closedWedge k (l + m + 1) α (closedWedge l m β γ) := by
  let hAB : (k + 1) + (l + 1) = (k + l + 1) + 1 := by omega
  let hBC : (l + 1) + (m + 1) = (l + m + 1) + 1 := by omega
  let hL : ((k + l + 1) + 1) + (m + 1) =
      ((k + l + 1) + m + 1) + 1 := by omega
  let hR : (k + 1) + ((l + m + 1) + 1) =
      (k + (l + m + 1) + 1) + 1 := by omega
  let hClass : (k + l + 1) + m + 1 = k + (l + m + 1) + 1 := by omega
  apply Subtype.ext
  apply Subtype.ext
  rw [castClosed_form]
  change castForm (congrArg Nat.succ hClass)
      (castForm hL
        (formWedge (castForm hAB (formWedge α.1.1 β.1.1)) γ.1.1)) =
    castForm hR
      (formWedge α.1.1 (castForm hBC (formWedge β.1.1 γ.1.1)))
  rw [formWedge_cast_left, formWedge_cast_right]
  rw [castForm_comp, castForm_comp]
  have hassoc := formWedge_assoc α.1.1 β.1.1 γ.1.1
  rw [← hassoc]
  simp only [castForm_comp]

theorem closedWedge_swap (k l : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    castClosed
      (show l + k + 1 = k + l + 1 by omega)
      (closedWedge l k β α) =
        (-1 : ℝ) ^ ((k + 1) * (l + 1)) • closedWedge k l α β := by
  let hBA : (l + 1) + (k + 1) = (l + k + 1) + 1 := by omega
  let hAB : (k + 1) + (l + 1) = (k + l + 1) + 1 := by omega
  let hClass : l + k + 1 = k + l + 1 := by omega
  apply Subtype.ext
  apply Subtype.ext
  rw [castClosed_form]
  change castForm (congrArg Nat.succ hClass)
      (castForm hBA (formWedge β.1.1 α.1.1)) =
    (-1 : ℝ) ^ ((k + 1) * (l + 1)) •
      castForm hAB (formWedge α.1.1 β.1.1)
  rw [castForm_comp, ← castForm_smul]
  have hswap := formWedge_swap (Nat.zero_lt_succ k)
    (Nat.zero_lt_succ l) α.1.1 β.1.1
  rw [← hswap]
  simp only [castForm_comp]

theorem cohomologyWedge_assoc (k l m : ℕ)
    (a : positiveDegreeCohomology (E := E) (M₀ := M) k)
    (b : positiveDegreeCohomology (E := E) (M₀ := M) l)
    (c : positiveDegreeCohomology (E := E) (M₀ := M) m) :
    castClass
      (show (k + l + 1) + m + 1 = k + (l + m + 1) + 1 by omega)
      (cohomologyWedge (k + l + 1) m (cohomologyWedge k l a b) c) =
        cohomologyWedge k (l + m + 1) a (cohomologyWedge l m b c) := by
  refine QuotientAddGroup.induction_on a ?_
  intro α
  refine QuotientAddGroup.induction_on b ?_
  intro β
  refine QuotientAddGroup.induction_on c ?_
  intro γ
  simp only [cohomologyWedge_mk, castClass_mk]
  change QuotientAddGroup.mk
      (castClosed (show (k + l + 1) + m + 1 =
        k + (l + m + 1) + 1 by omega)
        (closedWedge (k + l + 1) m (closedWedge k l α β) γ)) =
    QuotientAddGroup.mk
      (closedWedge k (l + m + 1) α (closedWedge l m β γ))
  rw [closedWedge_assoc]

theorem closedFormClass_smul (k : ℕ) (c : ℝ)
    (α : closedForms (E := E) (M₀ := M) (k + 1)) :
    closedFormClass k (c • α) = c • closedFormClass k α := rfl

theorem cohomologyWedge_swap (k l : ℕ)
    (a : positiveDegreeCohomology (E := E) (M₀ := M) k)
    (b : positiveDegreeCohomology (E := E) (M₀ := M) l) :
    castClass (show l + k + 1 = k + l + 1 by omega)
      (cohomologyWedge l k b a) =
        (-1 : ℝ) ^ ((k + 1) * (l + 1)) •
          cohomologyWedge k l a b := by
  refine QuotientAddGroup.induction_on a ?_
  intro α
  refine QuotientAddGroup.induction_on b ?_
  intro β
  simp only [cohomologyWedge_mk, castClass_mk]
  change QuotientAddGroup.mk
      (castClosed (show l + k + 1 = k + l + 1 by omega)
        (closedWedge l k β α)) =
    (-1 : ℝ) ^ ((k + 1) * (l + 1)) •
      QuotientAddGroup.mk (closedWedge k l α β)
  rw [closedWedge_swap]
  rfl

/-- The positive-degree wedge as a real bilinear map. -/
noncomputable def cohomologyWedgeBilinear (k l : ℕ) :
    positiveDegreeCohomology (E := E) (M₀ := M) k →ₗ[ℝ]
      positiveDegreeCohomology (E := E) (M₀ := M) l →ₗ[ℝ]
        positiveDegreeCohomology (E := E) (M₀ := M) (k + l + 1) where
  toFun a := {
    toFun := cohomologyWedge k l a
    map_add' := by intro b b'; exact cohomologyWedge_add_right k l a b b'
    map_smul' := by
      intro c b
      simpa only [← cohomologyScalar_eq_smul] using
        cohomologyWedge_smul_right k l c a b }
  map_add' := by
    intro a a'
    apply LinearMap.ext
    intro b
    exact cohomologyWedge_add_left k l a a' b
  map_smul' := by
    intro c a
    apply LinearMap.ext
    intro b
    simpa only [← cohomologyScalar_eq_smul] using
      cohomologyWedge_smul_left k l c a b

end QuaternionicSymmetry.ManifoldDeRhamRing
