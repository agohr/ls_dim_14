import QuaternionicSymmetry.QuaternionicLineProjection

/-! Local quaternionic Gram-Schmidt for smoothly varying invariant subspaces.
The initial frame is prescribed, and the construction remains inside the
original subspaces at every nearby parameter. -/
namespace QuaternionicSymmetry.QuaternionicLocalOrthonormalFrame
open QuaternionicStructure QuaternionicLineProjection Filter
open scoped ContDiff Topology
noncomputable section
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_local_frame (Q : QuaternionicStructure E) (n : ℕ)
    (f : Fin n → X → E) (a : X) (W : X → Submodule ℝ E)
    (hf : ∀ᶠ y in 𝓝 a, ∀ i, ContDiffAt ℝ ∞ (f i) y)
    (horth : Orthonormal ℝ (fun p : Fin n × Fin 4 => Q.frame (f p.1 a) p.2))
    (hW : ∀ᶠ y in 𝓝 a,
      (∀ z ∈ W y, Q.I z ∈ W y) ∧ (∀ z ∈ W y, Q.J z ∈ W y) ∧
      ∀ i, f i y ∈ W y) :
    ∃ u : Fin n → X → E,
      (∀ᶠ y in 𝓝 a, ∀ i, ContDiffAt ℝ ∞ (u i) y) ∧ (∀ i, u i a = f i a) ∧
      ∀ᶠ y in 𝓝 a, (∀ i, u i y ∈ W y) ∧
        Orthonormal ℝ (fun p : Fin n × Fin 4 => Q.frame (u p.1 y) p.2) := by
  classical
  induction n generalizing a W with
  | zero =>
    refine ⟨f,hf,fun _ => rfl,?_⟩
    exact Filter.Eventually.of_forall (fun y => ⟨fun i => Fin.elim0 i,
      orthonormal_iff_ite.mpr (fun p => Fin.elim0 p.1)⟩)
  | succ n ih =>
    have hnorm : ‖f 0 a‖ = 1 := horth.norm_eq_one (0,0)
    have hne : f 0 a ≠ 0 := by intro h; simp [h] at hnorm
    let v : X → E := fun y => normalize (f 0 y)
    have hv : ∀ᶠ y in 𝓝 a, ContDiffAt ℝ ∞ v y := by
      filter_upwards [hf,(hf.self_of_nhds 0).continuousAt.eventually_ne hne] with y hy hyne
      exact (normalize_contDiffAt hyne).comp y (hy 0)
    have hva : v a = f 0 a := by simp [v,QuaternionicLineProjection.normalize,hnorm]
    have hvnorm : ∀ᶠ y in 𝓝 a, ‖v y‖ = 1 :=
      ((hf.self_of_nhds 0).continuousAt.eventually_ne hne).mono fun y hy => normalize_norm _ hy
    let g : Fin n → X → E := fun i y => f i.succ y - projection Q (v y) (f i.succ y)
    have hg : ∀ᶠ y in 𝓝 a, ∀ i, ContDiffAt ℝ ∞ (g i) y := by
      filter_upwards [hf,hv] with y hy hyv
      exact fun i => (hy i.succ).sub
        (((projection_contDiff Q).contDiffAt.comp y hyv).clm_apply (hy i.succ))
    have hga (i : Fin n) : g i a = f i.succ a := by
      dsimp only [g]
      rw [hva,projection_eq_zero]
      · simp
      · intro k
        exact horth.inner_eq_zero (i := (0,k)) (j := (i.succ,0))
          (by intro h; exact Fin.succ_ne_zero i (congrArg Prod.fst h).symm)
    let U : X → Submodule ℝ E := fun y => W y ⊓ (Q.frameSpan (v y)).orthogonal
    have hgorth : Orthonormal ℝ (fun p : Fin n × Fin 4 => Q.frame (g p.1 a) p.2) := by
      simp only [hga]
      exact horth.comp (fun p : Fin n × Fin 4 => (p.1.succ,p.2))
        (by
          rintro ⟨i,k⟩ ⟨j,l⟩ h
          have hh : i.succ = j.succ ∧ k = l := Prod.mk.inj h
          exact Prod.ext (Fin.succ_inj.mp hh.1) hh.2)
    have hgU : ∀ᶠ y in 𝓝 a,
        (∀ z ∈ U y, Q.I z ∈ U y) ∧ (∀ z ∈ U y, Q.J z ∈ U y) ∧ ∀ i, g i y ∈ U y := by
      filter_upwards [hW,hvnorm] with y hy hyn
      have hvW : v y ∈ W y := (W y).smul_mem _ (hy.2.2 0)
      refine ⟨fun z hz => ⟨hy.1 z hz.1,Q.I_stable_frameSpan_orthogonal _ hz.2⟩,
        fun z hz => ⟨hy.2.1 z hz.1,Q.J_stable_frameSpan_orthogonal _ hz.2⟩,?_⟩
      intro i
      exact ⟨(W y).sub_mem (hy.2.2 i.succ) (projection_mem Q _ _ _ hy.1 hy.2.1 hvW),
        residual_mem_orthogonal Q _ hyn _⟩
    obtain ⟨u,hu,hua,huU⟩ := ih g a U hg hgorth hgU
    refine ⟨Fin.cons v u,?_,?_,?_⟩
    · filter_upwards [hv,hu] with y hyv hyu
      exact fun i => Fin.cases hyv hyu i
    · intro i
      exact Fin.cases hva (fun j => (hua j).trans (hga j)) i
    · filter_upwards [hW,hvnorm,huU] with y hy hyn hyu
      refine ⟨?_,?_⟩
      · intro i
        exact Fin.cases ((W y).smul_mem _ (hy.2.2 0)) (fun j => (hyu.1 j).1) i
      · rw [orthonormal_iff_ite]
        rintro ⟨i,k⟩ ⟨j,l⟩
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · simpa using (orthonormal_iff_ite.mp (Q.frame_orthonormal (v y) hyn) k l)
        · have hmem : Q.frame (u j y) l ∈ (Q.frameSpan (v y)).orthogonal := by
            fin_cases l
            · exact (hyu.1 j).2
            · exact Q.I_stable_frameSpan_orthogonal _ (hyu.1 j).2
            · exact Q.J_stable_frameSpan_orthogonal _ (hyu.1 j).2
            · exact Q.K_stable_frameSpan_orthogonal _ (hyu.1 j).2
          simpa using (Q.frameSpan (v y)).inner_right_of_mem_orthogonal
            (Submodule.subset_span ⟨k,rfl⟩) hmem
        · have hmem : Q.frame (u i y) k ∈ (Q.frameSpan (v y)).orthogonal := by
            fin_cases k
            · exact (hyu.1 i).2
            · exact Q.I_stable_frameSpan_orthogonal _ (hyu.1 i).2
            · exact Q.J_stable_frameSpan_orthogonal _ (hyu.1 i).2
            · exact Q.K_stable_frameSpan_orthogonal _ (hyu.1 i).2
          simpa using (Q.frameSpan (v y)).inner_left_of_mem_orthogonal
            (Submodule.subset_span ⟨l,rfl⟩) hmem
        · simpa using (orthonormal_iff_ite.mp hyu.2 (i,k) (j,l))

end
end QuaternionicSymmetry.QuaternionicLocalOrthonormalFrame
