import QuaternionicSymmetry.ComplexProjectiveHausdorff

/-! The existing coordinate-indexed separation proof works for every finite
index type, including the paired indices of the actual Sp model. The result
is a theorem rather than a global instance, avoiding chart-instance diamonds. -/

namespace QuaternionicSymmetry.FiniteComplexProjectiveHausdorff

open scoped Topology LinearAlgebra.Projectivization
noncomputable section

variable {ι : Type*} [Fintype ι]
private abbrev V (ι : Type*) := ι → ℂ

private theorem proportional_of_minors_zero
    (v w : V ι) (hw : w ≠ 0)
    (h : ∀ i j : ι, v i * w j = v j * w i) :
    ∃ a : ℂ, a • w = v := by
  have hsome : ∃ j : ι, w j ≠ 0 := by
    by_contra hn
    apply hw
    funext j
    by_contra hj
    exact hn ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hsome
  refine ⟨v j / w j, ?_⟩
  funext i
  change (v j / w j) * w i = v i
  calc
    (v j / w j) * w i = (v j * w i) / w j := by ring
    _ = (v i * w j) / w j := by rw [(h i j).symm]
    _ = v i := by field_simp [hj]

private theorem same_projective_iff_minors_zero
    (v w : {v : V ι // v ≠ 0}) :
    Projectivization.mk' ℂ v = Projectivization.mk' ℂ w ↔
      ∀ i j : ι, v.1 i * w.1 j = v.1 j * w.1 i := by
  rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk,
    Projectivization.mk_eq_mk_iff' ℂ v.1 w.1 v.2 w.2]
  constructor
  · rintro ⟨a, ha⟩ i j
    have hi := congrFun ha i
    have hj := congrFun ha j
    change v.1 i * w.1 j = v.1 j * w.1 i
    rw [← hi, ← hj]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · exact proportional_of_minors_zero v.1 w.1 w.2

private theorem isClosed_projective_relation :
    IsClosed {q : {v : V ι // v ≠ 0} × {v : V ι // v ≠ 0} |
      Projectivization.mk' ℂ q.1 = Projectivization.mk' ℂ q.2} := by
  have heq : {q : {v : V ι // v ≠ 0} × {v : V ι // v ≠ 0} |
      Projectivization.mk' ℂ q.1 = Projectivization.mk' ℂ q.2} =
      ⋂ i : ι, ⋂ j : ι,
        {q | q.1.1 i * q.2.1 j = q.1.1 j * q.2.1 i} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact same_projective_iff_minors_zero q.1 q.2
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  have hcoord₁ (i : ι) :
      Continuous (fun q : {v : V ι // v ≠ 0} × {v : V ι // v ≠ 0} =>
        q.1.1 i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
  have hcoord₂ (i : ι) :
      Continuous (fun q : {v : V ι // v ≠ 0} × {v : V ι // v ≠ 0} =>
        q.2.1 i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  exact isClosed_eq ((hcoord₁ i).mul (hcoord₂ j))
    ((hcoord₁ j).mul (hcoord₂ i))

private theorem isOpenMap_projectivization_mk :
    IsOpenMap (Projectivization.mk' ℂ :
      {v : V ι // v ≠ 0} → ℙ ℂ (V ι)) := by
  intro U hU
  change IsOpen[TopologicalSpace.coinduced (Projectivization.mk' ℂ)
    inferInstance] ((Projectivization.mk' ℂ) '' U)
  apply isOpen_coinduced.mpr
  have heq : (Projectivization.mk' ℂ : {v : V ι // v ≠ 0} → ℙ ℂ (V ι)) ⁻¹'
      ((Projectivization.mk' ℂ) '' U) =
      ⋃ a : ℂˣ, (fun v : {v : V ι // v ≠ 0} =>
        (⟨(a : ℂ) • v.1, by exact smul_ne_zero a.ne_zero v.2⟩ :
          {v : V ι // v ≠ 0})) ⁻¹' U := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw, hmk⟩
      obtain ⟨a, ha⟩ :=
        (Projectivization.mk_eq_mk_iff ℂ w.1 v.1 w.2 v.2).1 hmk
      refine ⟨a, ?_⟩
      convert hw using 1
      exact Subtype.ext ha
    · rintro ⟨a, ha⟩
      refine ⟨⟨(a : ℂ) • v.1, smul_ne_zero a.ne_zero v.2⟩, ha, ?_⟩
      change Projectivization.mk ℂ ((a : ℂ) • v.1) _ =
        Projectivization.mk ℂ v.1 v.2
      exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨a, rfl⟩
  rw [heq]
  apply isOpen_iUnion
  intro a
  apply hU.preimage
  apply Continuous.subtype_mk
  exact continuous_const.smul continuous_subtype_val

theorem t2Space (ι : Type*) [Fintype ι] : T2Space (ℙ ℂ (V ι)) := by
  have hOpen : IsOpenQuotientMap (Projectivization.mk' ℂ :
      {v : V ι // v ≠ 0} → ℙ ℂ (V ι)) :=
    ⟨Quotient.mk_surjective, continuous_quotient_mk',
      isOpenMap_projectivization_mk⟩
  exact (t2Space_iff_of_isOpenQuotientMap hOpen).2
    isClosed_projective_relation

end
end QuaternionicSymmetry.FiniteComplexProjectiveHausdorff
