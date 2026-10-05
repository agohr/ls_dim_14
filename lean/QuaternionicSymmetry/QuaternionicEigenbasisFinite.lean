import QuaternionicSymmetry.QuaternionicEigenbasisDimension

/-! Quaternionic eigenbases indexed by the intrinsic dimension. -/

namespace QuaternionicSymmetry.QuaternionicStructure

noncomputable section

theorem exists_eigenOrthonormalBasis_fin {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer) :
    ∃ (vals : Fin Q.quaternionicDimension → ℝ) (v : Fin Q.quaternionicDimension → V)
      (b : OrthonormalBasis (Fin Q.quaternionicDimension × Fin 4) ℝ V),
      (∀ p, b p = Q.frame (v p.1) p.2) ∧
      (∀ j, A (v j) = vals j • Q.I (v j)) := by
  classical
  obtain ⟨β, hβ, vals, v, b, hb, heig⟩ := Q.exists_eigenOrthonormalBasis A hA
  letI : Fintype β := hβ
  let e : β ≃ Fin Q.quaternionicDimension :=
    (Fintype.equivFin β).trans (finCongr (Q.card_eq_quaternionicDimension_of_orthonormalBasis b))
  refine ⟨vals ∘ e.symm, v ∘ e.symm, b.reindex (Equiv.prodCongr e (Equiv.refl _)), ?_, ?_⟩
  · rintro ⟨j, k⟩
    simpa only [OrthonormalBasis.reindex_apply, Equiv.prodCongr_symm,
      Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply] using
      hb (e.symm j, k)
  · intro j
    exact heig (e.symm j)

end
end QuaternionicSymmetry.QuaternionicStructure
