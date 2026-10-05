import QuaternionicSymmetry.HyperholomorphicForms

/-!
  Quaternionic Hermitian linear algebra.

  This file records the pointwise quaternion relations and their elementary
  consequences for an inner product.  It does not assert any spectral sign or
  geometric result.
-/

namespace QuaternionicSymmetry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A pair of orthogonal complex structures satisfying the quaternion relation. -/
structure QuaternionicStructure (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  I : V ≃ₗᵢ[ℝ] V
  J : V ≃ₗᵢ[ℝ] V
  I_sq : ∀ v : V, I (I v) = -v
  J_sq : ∀ v : V, J (J v) = -v
  I_J_anti : ∀ v : V, I (J v) = -J (I v)

namespace QuaternionicStructure

/-- The third quaternionic complex structure, `K = I ∘ J`. -/
def K (Q : QuaternionicStructure V) : V ≃ₗᵢ[ℝ] V := Q.J.trans Q.I

@[simp] theorem K_apply (Q : QuaternionicStructure V) (v : V) : Q.K v = Q.I (Q.J v) := rfl

theorem J_I_anti (Q : QuaternionicStructure V) (v : V) : Q.J (Q.I v) = -Q.I (Q.J v) := by
  simpa using (congrArg Neg.neg (Q.I_J_anti v)).symm

theorem K_sq (Q : QuaternionicStructure V) (v : V) : Q.K (Q.K v) = -v := by
  change Q.I (Q.J (Q.I (Q.J v))) = -v
  rw [Q.I_J_anti, Q.I_sq]
  simp [Q.J_sq]

theorem I_K_anti (Q : QuaternionicStructure V) (v : V) : Q.I (Q.K v) = -Q.K (Q.I v) := by
  change Q.I (Q.I (Q.J v)) = -Q.I (Q.J (Q.I v))
  rw [Q.I_sq, Q.I_J_anti, Q.I_sq]
  simp

theorem K_I_anti (Q : QuaternionicStructure V) (v : V) : Q.K (Q.I v) = -Q.I (Q.K v) := by
  simpa using (congrArg Neg.neg (Q.I_K_anti v)).symm

theorem J_K_anti (Q : QuaternionicStructure V) (v : V) : Q.J (Q.K v) = -Q.K (Q.J v) := by
  change Q.J (Q.I (Q.J v)) = -Q.I (Q.J (Q.J v))
  rw [Q.J_I_anti, Q.J_sq]

theorem K_J_anti (Q : QuaternionicStructure V) (v : V) : Q.K (Q.J v) = -Q.J (Q.K v) := by
  simpa using (congrArg Neg.neg (Q.J_K_anti v)).symm

private theorem skew_of_sq_neg (E : V ≃ₗᵢ[ℝ] V) (hE : ∀ v : V, E (E v) = -v)
    (v w : V) : inner ℝ (E v) w = -inner ℝ v (E w) := by
  have hw : E (-E w) = w := by
    rw [map_neg, hE]
    simp
  calc
    inner ℝ (E v) w = inner ℝ (E v) (E (-E w)) := by rw [hw]
    _ = inner ℝ v (-E w) := E.inner_map_map _ _
    _ = -inner ℝ v (E w) := by simp

theorem I_skew (Q : QuaternionicStructure V) (v w : V) :
    inner ℝ (Q.I v) w = -inner ℝ v (Q.I w) :=
  skew_of_sq_neg Q.I Q.I_sq v w

theorem J_skew (Q : QuaternionicStructure V) (v w : V) :
    inner ℝ (Q.J v) w = -inner ℝ v (Q.J w) :=
  skew_of_sq_neg Q.J Q.J_sq v w

theorem K_skew (Q : QuaternionicStructure V) (v w : V) :
    inner ℝ (Q.K v) w = -inner ℝ v (Q.K w) :=
  skew_of_sq_neg Q.K Q.K_sq v w

theorem commute_K (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hI : ∀ v : V, A (Q.I v) = Q.I (A v))
    (hJ : ∀ v : V, A (Q.J v) = Q.J (A v)) (v : V) :
    A (Q.K v) = Q.K (A v) := by
  change A (Q.I (Q.J v)) = Q.I (Q.J (A v))
  rw [hI, hJ]

theorem theta_invariant_I (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hskew : ∀ v w : V, inner ℝ (A v) w = -inner ℝ v (A w))
    (hI : ∀ v : V, A (Q.I v) = Q.I (A v)) (v : Fin 2 → V) :
    HyperholomorphicForms.theta A hskew (fun i => Q.I (v i)) =
      HyperholomorphicForms.theta A hskew v :=
  HyperholomorphicForms.theta_invariant A hskew Q.I.toLinearIsometry hI v

theorem theta_invariant_J (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hskew : ∀ v w : V, inner ℝ (A v) w = -inner ℝ v (A w))
    (hJ : ∀ v : V, A (Q.J v) = Q.J (A v)) (v : Fin 2 → V) :
    HyperholomorphicForms.theta A hskew (fun i => Q.J (v i)) =
      HyperholomorphicForms.theta A hskew v :=
  HyperholomorphicForms.theta_invariant A hskew Q.J.toLinearIsometry hJ v

theorem theta_invariant_K (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hskew : ∀ v w : V, inner ℝ (A v) w = -inner ℝ v (A w))
    (hI : ∀ v : V, A (Q.I v) = Q.I (A v))
    (hJ : ∀ v : V, A (Q.J v) = Q.J (A v)) (v : Fin 2 → V) :
    HyperholomorphicForms.theta A hskew (fun i => Q.K (v i)) =
      HyperholomorphicForms.theta A hskew v :=
  HyperholomorphicForms.theta_invariant A hskew Q.K.toLinearIsometry (Q.commute_K A hI hJ) v

/-- Skew-adjoint real-linear endomorphisms commuting with the quaternionic structure. -/
def skewCentralizer (Q : QuaternionicStructure V) : Submodule ℝ (V →ₗ[ℝ] V) where
  carrier := {A | (∀ v w : V, inner ℝ (A v) w = -inner ℝ v (A w)) ∧
    (∀ v : V, A (Q.I v) = Q.I (A v)) ∧ (∀ v : V, A (Q.J v) = Q.J (A v))}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro v w
      simp
    · intro v
      simp
    · intro v
      simp
  add_mem' := by
    rintro A B ⟨hAs, hAI, hAJ⟩ ⟨hBs, hBI, hBJ⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v w
      simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hAs, hBs]
      ring
    · intro v
      simp only [LinearMap.add_apply, hAI, hBI, map_add]
    · intro v
      simp only [LinearMap.add_apply, hAJ, hBJ, map_add]
  smul_mem' := by
    rintro c A ⟨hAs, hAI, hAJ⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v w
      simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, hAs]
      simp only [starRingEnd_apply, star_trivial]
      ring
    · intro v
      simp only [LinearMap.smul_apply, hAI, map_smul]
    · intro v
      simp only [LinearMap.smul_apply, hAJ, map_smul]

theorem mem_skewCentralizer_iff (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V) :
    A ∈ Q.skewCentralizer ↔ (∀ v w : V, inner ℝ (A v) w = -inner ℝ v (A w)) ∧
      (∀ v : V, A (Q.I v) = Q.I (A v)) ∧ (∀ v : V, A (Q.J v) = Q.J (A v)) :=
  Iff.rfl

end QuaternionicStructure
end QuaternionicSymmetry
