import QuaternionicSymmetry.ManifoldDeRhamDegreeZero

/-!
All-degree de Rham products. The zero-degree piece is represented directly by
closed zero-forms, while positive degrees use the existing closed/exact quotient.
-/

namespace QuaternionicSymmetry.ManifoldDeRhamAllDegrees

open QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldDeRhamWedge
  QuaternionicSymmetry.ManifoldDeRhamRing
  QuaternionicSymmetry.ManifoldDeRhamDegreeZero
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 500000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Normalized wedge of smooth closed forms in arbitrary degrees. -/
noncomputable def closedWedgeAll {p q : ℕ}
    (α : closedForms (E := E) (M₀ := M) p)
    (β : closedForms (E := E) (M₀ := M) q) :
    closedForms (E := E) (M₀ := M) (p + q) := by
  have hcα : exteriorDerivative α.1.1 = 0 :=
    congrArg Subtype.val α.2
  have hcβ : exteriorDerivative β.1.1 = 0 :=
    congrArg Subtype.val β.2
  refine ⟨⟨formWedge α.1.1 β.1.1,
    chartSmooth_formWedge α.1.1 β.1.1 α.1.2 β.1.2⟩, ?_⟩
  change smoothExteriorDerivative (E := E) (M₀ := M) (p + q)
    ⟨formWedge α.1.1 β.1.1,
      chartSmooth_formWedge α.1.1 β.1.1 α.1.2 β.1.2⟩ = 0
  apply Subtype.ext
  exact formWedge_closed α.1.1 β.1.1 α.1.2 β.1.2 hcα hcβ

noncomputable def castClosedDegree {p q : ℕ} (h : p = q)
    (α : closedForms (E := E) (M₀ := M) p) :
    closedForms (E := E) (M₀ := M) q := by
  cases h
  exact α

theorem castClosedDegree_form {p q : ℕ} (h : p = q)
    (α : closedForms (E := E) (M₀ := M) p) :
    (castClosedDegree h α).1.1 = castForm h α.1.1 := by
  cases h
  rfl

theorem castClosedDegree_sub {p q : ℕ} (h : p = q)
    (α β : closedForms (E := E) (M₀ := M) p) :
    castClosedDegree h (α - β) =
      castClosedDegree h α - castClosedDegree h β := by
  cases h
  rfl

theorem closedWedgeAll_sub_left {p q : ℕ}
    (α₁ α₂ : closedForms (E := E) (M₀ := M) p)
    (β : closedForms (E := E) (M₀ := M) q) :
    closedWedgeAll (α₁ - α₂) β =
      closedWedgeAll α₁ β - closedWedgeAll α₂ β := by
  apply Subtype.ext
  apply Subtype.ext
  exact formWedge_sub_left α₁.1.1 α₂.1.1 β.1.1

theorem closedWedgeAll_sub_right {p q : ℕ}
    (α : closedForms (E := E) (M₀ := M) p)
    (β₁ β₂ : closedForms (E := E) (M₀ := M) q) :
    closedWedgeAll α (β₁ - β₂) =
      closedWedgeAll α β₁ - closedWedgeAll α β₂ := by
  apply Subtype.ext
  apply Subtype.ext
  exact formWedge_sub_right α.1.1 β₁.1.1 β₂.1.1

/-- A zero-degree closed form wedges a positive closed form. -/
noncomputable def zeroPositiveClosed (l : ℕ)
    (a : zeroDegreeCohomology (E := E) (M := M))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    closedForms (E := E) (M₀ := M) (l + 1) :=
  castClosedDegree (Nat.zero_add (l + 1)) (closedWedgeAll a β)

/-- A positive closed form wedges a zero-degree closed form. -/
noncomputable def positiveZeroClosed (k : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (a : zeroDegreeCohomology (E := E) (M := M)) :
    closedForms (E := E) (M₀ := M) (k + 1) :=
  closedWedgeAll (p := k + 1) (q := 0) α a

theorem zeroPositiveClosed_sub (l : ℕ)
    (a : zeroDegreeCohomology (E := E) (M := M))
    (β₁ β₂ : closedForms (E := E) (M₀ := M) (l + 1)) :
    zeroPositiveClosed l a (β₁ - β₂) =
      zeroPositiveClosed l a β₁ - zeroPositiveClosed l a β₂ := by
  unfold zeroPositiveClosed
  rw [closedWedgeAll_sub_right, castClosedDegree_sub]

theorem positiveZeroClosed_sub (k : ℕ)
    (α₁ α₂ : closedForms (E := E) (M₀ := M) (k + 1))
    (a : zeroDegreeCohomology (E := E) (M := M)) :
    positiveZeroClosed k (α₁ - α₂) a =
      positiveZeroClosed k α₁ a - positiveZeroClosed k α₂ a := by
  exact closedWedgeAll_sub_left (p := k + 1) (q := 0) α₁ α₂ a

theorem zeroPositiveClosed_exact (l : ℕ)
    (a : zeroDegreeCohomology (E := E) (M := M))
    (β : closedForms (E := E) (M₀ := M) (l + 1))
    (hβ : β ∈ exactClosedAddSubgroup (E := E) (M₀ := M) l) :
    zeroPositiveClosed l a β ∈ exactClosedAddSubgroup (E := E) (M₀ := M) l := by
  change (β.1 : smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := l + 1)) ∈
    exactForms (E := E) (M₀ := M) l at hβ
  rcases hβ with ⟨η, hη⟩
  have hform : exteriorDerivative η.1 = β.1.1 := congrArg Subtype.val hη
  have hc : exteriorDerivative a.1.1 = 0 := congrArg Subtype.val a.2
  change (zeroPositiveClosed l a β).1 ∈ exactForms (E := E) (M₀ := M) l
  let hprim : 0 + l = l := Nat.zero_add l
  let primitive : smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := l) :=
    ⟨castForm hprim (formWedge a.1.1 η.1),
      chartSmooth_castForm hprim _
        (chartSmooth_formWedge a.1.1 η.1 a.1.2 η.2)⟩
  refine ⟨primitive, ?_⟩
  apply Subtype.ext
  dsimp [primitive, smoothExteriorDerivative]
  change exteriorDerivative (castForm hprim (formWedge a.1.1 η.1)) =
    (castClosedDegree (Nat.zero_add (l + 1)) (closedWedgeAll a β)).1.1
  rw [castClosedDegree_form]
  change exteriorDerivative (castForm hprim (formWedge a.1.1 η.1)) =
    castForm (Nat.zero_add (l + 1)) (formWedge a.1.1 β.1.1)
  rw [← hform, exteriorDerivative_castForm]
  rw [exteriorDerivative_formWedge_right a.1.1 η.1 a.1.2 η.2 hc]
  simp only [pow_zero, one_smul]

theorem positiveZeroClosed_exact (k : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (a : zeroDegreeCohomology (E := E) (M := M))
    (hα : α ∈ exactClosedAddSubgroup (E := E) (M₀ := M) k) :
    positiveZeroClosed k α a ∈ exactClosedAddSubgroup (E := E) (M₀ := M) k := by
  change (α.1 : smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := k + 1)) ∈
    exactForms (E := E) (M₀ := M) k at hα
  rcases hα with ⟨η, hη⟩
  have hform : exteriorDerivative η.1 = α.1.1 := congrArg Subtype.val hη
  have hc : exteriorDerivative a.1.1 = 0 := congrArg Subtype.val a.2
  change (positiveZeroClosed k α a).1 ∈ exactForms (E := E) (M₀ := M) k
  let primitive : smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := k) :=
    ⟨formWedge η.1 a.1.1,
      chartSmooth_formWedge η.1 a.1.1 η.2 a.1.2⟩
  refine ⟨primitive, ?_⟩
  apply Subtype.ext
  change exteriorDerivative (formWedge η.1 a.1.1) =
    formWedge α.1.1 a.1.1
  rw [← hform]
  exact (formWedge_exteriorDerivative_left η.1 a.1.1 η.2 a.1.2 hc).symm

/-- Multiplication of a positive-degree class by a zero-degree class on the left. -/
noncomputable def zeroPositiveWedge (l : ℕ)
    (a : zeroDegreeCohomology (E := E) (M := M)) :
    positiveDegreeCohomology (E := E) (M₀ := M) l →
      positiveDegreeCohomology (E := E) (M₀ := M) l :=
  fun b => Quotient.liftOn b
    (fun β => QuotientAddGroup.mk (zeroPositiveClosed l a β))
    (by
      intro β γ h
      have hd : β - γ ∈ exactClosedAddSubgroup (E := E) (M₀ := M) l := by
        have hh := QuotientAddGroup.leftRel_apply.mp h
        have hh' := (exactClosedAddSubgroup (E := E) (M₀ := M) l).neg_mem hh
        convert hh' using 1; abel
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      rw [← zeroPositiveClosed_sub]
      exact zeroPositiveClosed_exact l a (β - γ) hd)

/-- Multiplication of a positive-degree class by a zero-degree class on the right. -/
noncomputable def positiveZeroWedge (k : ℕ)
    (b : positiveDegreeCohomology (E := E) (M₀ := M) k)
    (a : zeroDegreeCohomology (E := E) (M := M)) :
    positiveDegreeCohomology (E := E) (M₀ := M) k :=
  Quotient.liftOn b
    (fun α => QuotientAddGroup.mk (positiveZeroClosed k α a))
    (by
      intro α γ h
      have hd : α - γ ∈ exactClosedAddSubgroup (E := E) (M₀ := M) k := by
        have hh := QuotientAddGroup.leftRel_apply.mp h
        have hh' := (exactClosedAddSubgroup (E := E) (M₀ := M) k).neg_mem hh
        convert hh' using 1; abel
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      rw [← positiveZeroClosed_sub]
      exact positiveZeroClosed_exact k (α - γ) a hd)

theorem zeroPositiveWedge_mk (l : ℕ)
    (a : zeroDegreeCohomology (E := E) (M := M))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    zeroPositiveWedge l a (QuotientAddGroup.mk β) =
      QuotientAddGroup.mk (zeroPositiveClosed l a β) := rfl

theorem positiveZeroWedge_mk (k : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (a : zeroDegreeCohomology (E := E) (M := M)) :
    positiveZeroWedge k (QuotientAddGroup.mk α) a =
      QuotientAddGroup.mk (positiveZeroClosed k α a) := rfl

theorem closedWedgeAll_one_left {n : ℕ}
    (α : closedForms (E := E) (M₀ := M) n) :
    castClosedDegree (Nat.zero_add n)
      (closedWedgeAll (oneClass (E := E) (M := M)) α) = α := by
  apply Subtype.ext
  apply Subtype.ext
  rw [castClosedDegree_form]
  exact formWedge_one_left α.1.1

theorem closedWedgeAll_one_right {n : ℕ}
    (α : closedForms (E := E) (M₀ := M) n) :
    closedWedgeAll α (oneClass (E := E) (M := M)) = α := by
  apply Subtype.ext
  apply Subtype.ext
  exact formWedge_one_right α.1.1

/-- Multiplication in degree zero is the ordinary wedge of closed zero-forms. -/
noncomputable def zeroZeroWedge
    (a b : zeroDegreeCohomology (E := E) (M := M)) :
    zeroDegreeCohomology (E := E) (M := M) :=
  closedWedgeAll (p := 0) (q := 0) a b

theorem zeroZeroWedge_one_left
    (a : zeroDegreeCohomology (E := E) (M := M)) :
    zeroZeroWedge (oneClass (E := E) (M := M)) a = a := by
  exact closedWedgeAll_one_left a

theorem zeroZeroWedge_one_right
    (a : zeroDegreeCohomology (E := E) (M := M)) :
    zeroZeroWedge a (oneClass (E := E) (M := M)) = a := by
  exact closedWedgeAll_one_right a

theorem zeroPositiveWedge_one_left (l : ℕ)
    (b : positiveDegreeCohomology (E := E) (M₀ := M) l) :
    zeroPositiveWedge l (oneClass (E := E) (M := M)) b = b := by
  induction b using Quotient.inductionOn with
  | _ β =>
    rw [zeroPositiveWedge_mk]
    congr 1
    exact closedWedgeAll_one_left β

theorem positiveZeroWedge_one_right (k : ℕ)
    (b : positiveDegreeCohomology (E := E) (M₀ := M) k) :
    positiveZeroWedge k b (oneClass (E := E) (M := M)) = b := by
  induction b using Quotient.inductionOn with
  | _ α =>
    rw [positiveZeroWedge_mk]
    congr 1
    exact closedWedgeAll_one_right α

/-- Degree-indexed de Rham groups, including degree zero. -/
def CohomologyByDegree (n : ℕ) : Type _ :=
  match n with
  | 0 => zeroDegreeCohomology (E := E) (M := M)
  | k + 1 => positiveDegreeCohomology (E := E) (M₀ := M) k

/-- The homogeneous degree-indexed cup product. -/
noncomputable def wedgeDegree : (p q : ℕ) →
    CohomologyByDegree (E := E) (M := M) p →
    CohomologyByDegree (E := E) (M := M) q →
    CohomologyByDegree (E := E) (M := M) (p + q)
  | 0, 0, a, b => zeroZeroWedge a b
  | 0, l + 1, a, b => by
      simpa only [Nat.zero_add] using zeroPositiveWedge l a b
  | k + 1, 0, a, b => positiveZeroWedge k a b
  | k + 1, l + 1, a, b =>
      castClass (show k + l + 1 = (k + 1) + l by omega)
        (cohomologyWedge k l a b)

/-- The homogeneous unit in degree zero. -/
noncomputable def unitDegree : CohomologyByDegree (E := E) (M := M) 0 :=
  oneClass (E := E) (M := M)

noncomputable def castDegree {p q : ℕ} (h : p = q)
    (a : CohomologyByDegree (E := E) (M := M) p) :
    CohomologyByDegree (E := E) (M := M) q := by
  cases h
  exact a

end QuaternionicSymmetry.ManifoldDeRhamAllDegrees
