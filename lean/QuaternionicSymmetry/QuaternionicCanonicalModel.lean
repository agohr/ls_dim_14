import QuaternionicSymmetry.QuaternionicStructureIsometryTransport
import QuaternionicSymmetry.QuaternionicMatrixModel

/-! Isometric quaternionic coordinates on the canonical complex matrix model.
The coordinate choice depends only on the structure, not on a curvature value. -/
namespace QuaternionicSymmetry.QuaternionicCanonicalModel
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_intertwiningIsometry_of_dimension
    (S : QuaternionicStructure E) (T : QuaternionicStructure F)
    (hdim : S.quaternionicDimension = T.quaternionicDimension) :
    ∃ U : E ≃ₗᵢ[ℝ] F,
      (∀ v, U (S.I v) = T.I (U v)) ∧
      (∀ v, U (S.J v) = T.J (U v)) := by
  classical
  obtain ⟨_, vS, bS, hbS, _⟩ :=
    S.exists_eigenOrthonormalBasis_fin 0 S.skewCentralizer.zero_mem
  obtain ⟨_, vT, bT, hbT, _⟩ :=
    T.exists_eigenOrthonormalBasis_fin 0 T.skewCentralizer.zero_mem
  let e : Fin S.quaternionicDimension ≃ Fin T.quaternionicDimension :=
    finCongr hdim
  let U : E ≃ₗᵢ[ℝ] F :=
    bS.equiv bT (Equiv.prodCongr e (Equiv.refl _))
  have hUb (j : Fin S.quaternionicDimension) (k : Fin 4) :
      U (S.frame (vS j) k) = T.frame (vT (e j)) k := by
    rw [← hbS (j, k), OrthonormalBasis.equiv_apply_basis]
    exact hbT (e j, k)
  have hU0 (j : Fin S.quaternionicDimension) :
      U (vS j) = vT (e j) := by
    simpa [QuaternionicStructure.frame] using hUb j 0
  have hU1 (j : Fin S.quaternionicDimension) :
      U (S.I (vS j)) = T.I (vT (e j)) := by
    simpa [QuaternionicStructure.frame] using hUb j 1
  have hU2 (j : Fin S.quaternionicDimension) :
      U (S.J (vS j)) = T.J (vT (e j)) := by
    simpa [QuaternionicStructure.frame] using hUb j 2
  have hU3 (j : Fin S.quaternionicDimension) :
      U (S.K (vS j)) = T.K (vT (e j)) := by
    simpa [QuaternionicStructure.frame] using hUb j 3
  have hIgen (j : Fin S.quaternionicDimension) (k : Fin 4) :
      U (S.I (S.frame (vS j) k)) =
        T.I (U (S.frame (vS j) k)) := by
    fin_cases k
    · change U (S.I (vS j)) = T.I (U (vS j))
      rw [hU0, hU1]
    · change U (S.I (S.I (vS j))) = T.I (U (S.I (vS j)))
      rw [S.I_sq, map_neg, hU0, hU1, T.I_sq]
    · change U (S.K (vS j)) = T.I (U (S.J (vS j)))
      rw [hU3, hU2]
      rfl
    · change U (S.I (S.K (vS j))) = T.I (U (S.K (vS j)))
      change U (S.I (S.I (S.J (vS j)))) =
        T.I (U (S.K (vS j)))
      rw [S.I_sq, map_neg, hU2, hU3]
      change -T.J (vT (e j)) = T.I (T.I (T.J (vT (e j))))
      rw [T.I_sq]
  have hJgen (j : Fin S.quaternionicDimension) (k : Fin 4) :
      U (S.J (S.frame (vS j) k)) =
        T.J (U (S.frame (vS j) k)) := by
    fin_cases k
    · change U (S.J (vS j)) = T.J (U (vS j))
      rw [hU0, hU2]
    · change U (S.J (S.I (vS j))) = T.J (U (S.I (vS j)))
      rw [S.J_I_anti, map_neg]
      change -U (S.K (vS j)) = T.J (U (S.I (vS j)))
      rw [hU3, hU1, T.J_I_anti]
      rfl
    · change U (S.J (S.J (vS j))) = T.J (U (S.J (vS j)))
      rw [S.J_sq, map_neg, hU0, hU2, T.J_sq]
    · change U (S.J (S.K (vS j))) = T.J (U (S.K (vS j)))
      change U (S.J (S.I (S.J (vS j)))) =
        T.J (U (S.K (vS j)))
      rw [S.J_I_anti, S.J_sq]
      simp only [map_neg, neg_neg]
      rw [hU1, hU3]
      change T.I (vT (e j)) = T.J (T.I (T.J (vT (e j))))
      rw [T.J_I_anti, T.J_sq]
      simp
  refine ⟨U, ?_, ?_⟩
  · intro x
    have hmaps : U.toLinearEquiv.toLinearMap.comp S.I.toLinearEquiv.toLinearMap =
        T.I.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap := by
      apply bS.toBasis.ext
      rintro ⟨j, k⟩
      change U (S.I (bS (j, k))) = T.I (U (bS (j, k)))
      rw [hbS]
      exact hIgen j k
    exact congrArg (fun f : E →ₗ[ℝ] F => f x) hmaps
  · intro x
    have hmaps : U.toLinearEquiv.toLinearMap.comp S.J.toLinearEquiv.toLinearMap =
        T.J.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap := by
      apply bS.toBasis.ext
      rintro ⟨j, k⟩
      change U (S.J (bS (j, k))) = T.J (U (bS (j, k)))
      rw [hbS]
      exact hJgen j k
    exact congrArg (fun f : E →ₗ[ℝ] F => f x) hmaps


/-- A single quaternionic isometry transports an arbitrary finite-dimensional
quaternionic Hermitian space to the fixed complex symplectic matrix model. -/
theorem exists_canonicalModel (S : QuaternionicStructure E) :
    ∃ U : E ≃ₗᵢ[ℝ] QuaternionicMatrixModel.V S.quaternionicDimension,
      (∀ v, U (S.I v) = QuaternionicMatrixModel.standardI S.quaternionicDimension (U v)) ∧
      (∀ v, U (S.J v) = QuaternionicMatrixModel.standardJ S.quaternionicDimension (U v)) := by
  apply exists_intertwiningIsometry_of_dimension S
    (QuaternionicMatrixModel.standardQuaternionicStructure S.quaternionicDimension)
  exact (QuaternionicMatrixModel.standardQuaternionicDimension _).symm

def canonicalModel (S : QuaternionicStructure E) :
    E ≃ₗᵢ[ℝ] QuaternionicMatrixModel.V S.quaternionicDimension :=
  Classical.choose (exists_canonicalModel S)

theorem canonicalModel_I (S : QuaternionicStructure E) (v : E) :
    canonicalModel S (S.I v) =
      QuaternionicMatrixModel.standardI S.quaternionicDimension (canonicalModel S v) :=
  (Classical.choose_spec (exists_canonicalModel S)).1 v

theorem canonicalModel_J (S : QuaternionicStructure E) (v : E) :
    canonicalModel S (S.J v) =
      QuaternionicMatrixModel.standardJ S.quaternionicDimension (canonicalModel S v) :=
  (Classical.choose_spec (exists_canonicalModel S)).2 v

end
end QuaternionicSymmetry.QuaternionicCanonicalModel
