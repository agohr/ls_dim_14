import QuaternionicSymmetry.QuaternionicEigenline
import QuaternionicSymmetry.QuaternionicRestriction
import QuaternionicSymmetry.OrthonormalAssembly

/-! A finite orthonormal quaternionic eigenbasis for skew centralizer elements. -/

namespace QuaternionicSymmetry
namespace QuaternionicStructure

noncomputable section

private theorem eigenbasis_aux (n : ℕ) :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [FiniteDimensional ℝ V] (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
      (_hA : A ∈ Q.skewCentralizer), Module.finrank ℝ V = n →
      ∃ (β : Type) (_ : Finite β) (vals : β → ℝ) (v : β → V),
        Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2) ∧
        Submodule.span ℝ (Set.range (fun p : β × Fin 4 => Q.frame (v p.1) p.2)) = ⊤ ∧
        ∀ j, A (v j) = vals j • Q.I (v j) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V _ _ _ Q A hA hdim
      by_cases hV : Nontrivial V
      · letI : Nontrivial V := hV
        obtain ⟨lam, v, hv, hev⟩ := Q.exists_unit_eigenline A hA
        let S : Submodule ℝ V := Q.frameSpan v
        let W : Submodule ℝ V := S.orthogonal
        have hIW : ∀ ⦃x : V⦄, x ∈ W → Q.I x ∈ W := by
          intro x hx
          exact Q.I_stable_frameSpan_orthogonal v hx
        have hJW : ∀ ⦃x : V⦄, x ∈ W → Q.J x ∈ W := by
          intro x hx
          exact Q.J_stable_frameSpan_orthogonal v hx
        have hAW : ∀ ⦃x : V⦄, x ∈ W → A x ∈ W := by
          intro x hx
          exact Q.eigenline_stable_orthogonal A hA hev hx
        let QW : QuaternionicStructure W := Q.restrict W hIW hJW
        let AW : W →ₗ[ℝ] W := restrictEndomorphism A W hAW
        have hAWQ : AW ∈ QW.skewCentralizer := by
          exact restrictEndomorphism_mem_skewCentralizer Q W hIW hJW A hA hAW
        have hlt : Module.finrank ℝ W < n := by
          rw [← hdim]
          exact Q.frameSpan_orthogonal_finrank_lt v hv
        obtain ⟨β, hβ, vals, w, horthW, hspanW, heigW⟩ :=
          ih (Module.finrank ℝ W) hlt QW AW hAWQ rfl
        letI : Finite β := hβ
        let vals' : Unit ⊕ β → ℝ := Sum.elim (fun _ => lam) vals
        let v' : Unit ⊕ β → V := Sum.elim (fun _ => v) (fun j => (w j : V))
        let f : Unit × Fin 4 → V := fun p => Q.frame v p.2
        let gW : β × Fin 4 → W := fun p => QW.frame (w p.1) p.2
        let g : β × Fin 4 → V := fun p => (gW p : V)
        have hf : Orthonormal ℝ f := by
          apply (Q.frame_orthonormal v hv).comp (fun p : Unit × Fin 4 => p.2)
          rintro ⟨u, i⟩ ⟨u', j⟩ hij
          have huu' : u = u' := Subsingleton.elim _ _
          cases huu'
          simpa using hij
        have hg : Orthonormal ℝ g := by
          rw [show g = W.subtypeₗᵢ ∘ gW by rfl]
          exact W.subtypeₗᵢ.orthonormal_comp_iff.mpr horthW
        have hfS : ∀ i, f i ∈ S := by
          rintro ⟨u, i⟩
          exact Submodule.subset_span ⟨i, rfl⟩
        have hgW : ∀ j, g j ∈ W := fun j => (gW j).property
        have horthSW : ∀ x ∈ S, ∀ y ∈ W, inner ℝ x y = 0 := by
          intro x hx y hy
          rw [real_inner_comm]
          exact (Submodule.mem_orthogonal' S y).mp hy x hx
        have horthSum : Orthonormal ℝ (OrthonormalAssembly.sumFamily f g) :=
          OrthonormalAssembly.orthonormal_sum_of_subspaces f g S W hf hg hfS hgW horthSW
        have hspanF : Submodule.span ℝ (Set.range f) = S := by
          have hrange : Set.range f = Set.range (Q.frame v) := by
            ext x
            constructor
            · rintro ⟨⟨u, i⟩, rfl⟩
              exact ⟨i, rfl⟩
            · rintro ⟨i, rfl⟩
              exact ⟨((), i), rfl⟩
          rw [hrange]
          rfl
        have hspanG : Submodule.span ℝ (Set.range g) = W := by
          apply le_antisymm
          · apply Submodule.span_le.mpr
            rintro x ⟨j, rfl⟩
            exact (gW j).property
          · intro x hx
            let xW : W := ⟨x, hx⟩
            have hxW : xW ∈ Submodule.span ℝ (Set.range gW) := by
              rw [hspanW]
              trivial
            have hmap : Submodule.map W.subtype (Submodule.span ℝ (Set.range gW)) ≤
                Submodule.span ℝ (Set.range g) := by
              rw [Submodule.map_span]
              apply Submodule.span_mono
              rintro y ⟨z, ⟨j, rfl⟩, rfl⟩
              exact ⟨j, rfl⟩
            exact hmap ⟨xW, hxW, rfl⟩
        have hspanSum : Submodule.span ℝ (Set.range (OrthonormalAssembly.sumFamily f g)) = ⊤ :=
          OrthonormalAssembly.span_sumFamily_eq_top f g S W hspanF hspanG
            (OrthonormalAssembly.sup_orthogonal_eq_top S)
        let e : ((Unit ⊕ β) × Fin 4) ≃ (Unit × Fin 4 ⊕ β × Fin 4) :=
          Equiv.sumProdDistrib Unit β (Fin 4)
        have hframeW (x : W) (i : Fin 4) : (QW.frame x i : V) = Q.frame (x : V) i := by
          fin_cases i <;> simp [QuaternionicStructure.frame, QW]
        have hfamily :
            (fun p : (Unit ⊕ β) × Fin 4 => Q.frame (v' p.1) p.2) =
              OrthonormalAssembly.sumFamily f g ∘ e := by
          funext p
          rcases p with ⟨u | j, i⟩
          · simp [e, v', f, OrthonormalAssembly.sumFamily]
          · change Q.frame (w j : V) i = (gW (j, i) : V)
            exact (hframeW (w j) i).symm
        refine ⟨Unit ⊕ β, inferInstance, vals', v', ?_, ?_, ?_⟩
        · rw [hfamily]
          exact horthSum.comp e e.injective
        · rw [hfamily]
          have hrange : Set.range (OrthonormalAssembly.sumFamily f g ∘ e) =
              Set.range (OrthonormalAssembly.sumFamily f g) := by
            ext x
            constructor
            · rintro ⟨p, rfl⟩
              exact ⟨e p, rfl⟩
            · rintro ⟨q, rfl⟩
              exact ⟨e.symm q, by simp⟩
          rw [hrange, hspanSum]
        · intro j
          rcases j with u | j
          · exact hev
          · have h := congrArg Subtype.val (heigW j)
            simpa [vals', v', AW, QW] using h
      · letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
        refine ⟨Empty, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
        · exact fun e => nomatch e
        · exact fun e => nomatch e
        · rw [orthonormal_iff_ite]
          rintro ⟨p, i⟩
          exact nomatch p
        · have htop : (⊤ : Submodule ℝ V) = ⊥ := by
            symm
            apply top_unique
            intro x hx
            have : x = 0 := Subsingleton.elim _ _
            simp [this]
          simp [htop]
        · intro e
          exact nomatch e

/-- A finite orthonormal basis of quaternionic eigenframes for every skew-centralizer element. -/
theorem exists_eigenbasis {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) :
    ∃ (β : Type) (_ : Finite β) (vals : β → ℝ) (v : β → V),
      Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2) ∧
      Submodule.span ℝ (Set.range (fun p : β × Fin 4 => Q.frame (v p.1) p.2)) = ⊤ ∧
      ∀ j, A (v j) = vals j • Q.I (v j) :=
  eigenbasis_aux (Module.finrank ℝ V) Q A hA rfl

end
end QuaternionicStructure
end QuaternionicSymmetry
