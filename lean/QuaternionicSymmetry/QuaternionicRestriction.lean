import QuaternionicSymmetry.QuaternionicStructure

/-! Restriction of quaternionic structures and their skew centralizers to invariant subspaces. -/

namespace QuaternionicSymmetry
namespace QuaternionicStructure

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private def restrictILinear (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hI : ∀ ⦃x : V⦄, x ∈ W → Q.I x ∈ W) : W →ₗ[ℝ] W where
  toFun x := ⟨Q.I x, hI x.property⟩
  map_add' x y := by
    ext
    exact Q.I.map_add x y
  map_smul' r x := by
    ext
    exact Q.I.map_smul r x

private theorem restrictILinear_bijective (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hI : ∀ ⦃x : V⦄, x ∈ W → Q.I x ∈ W) :
    Function.Bijective (restrictILinear Q W hI) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Q.I.injective
    exact congrArg Subtype.val hxy
  · intro y
    refine ⟨⟨-Q.I y, W.neg_mem (hI y.property)⟩, ?_⟩
    apply Subtype.ext
    change Q.I (-Q.I (y : V)) = y
    rw [map_neg, Q.I_sq]
    simp

/-- The restricted `I` isometry of an invariant submodule. -/
noncomputable def restrictI (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hI : ∀ ⦃x : V⦄, x ∈ W → Q.I x ∈ W) : W ≃ₗᵢ[ℝ] W :=
  LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective (restrictILinear Q W hI) (restrictILinear_bijective Q W hI))
    (fun x => by
      change ‖Q.I (x : V)‖ = ‖(x : V)‖
      exact Q.I.norm_map _)

private def restrictJLinear (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hJ : ∀ ⦃x : V⦄, x ∈ W → Q.J x ∈ W) : W →ₗ[ℝ] W where
  toFun x := ⟨Q.J x, hJ x.property⟩
  map_add' x y := by
    ext
    exact Q.J.map_add x y
  map_smul' r x := by
    ext
    exact Q.J.map_smul r x

private theorem restrictJLinear_bijective (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hJ : ∀ ⦃x : V⦄, x ∈ W → Q.J x ∈ W) :
    Function.Bijective (restrictJLinear Q W hJ) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Q.J.injective
    exact congrArg Subtype.val hxy
  · intro y
    refine ⟨⟨-Q.J y, W.neg_mem (hJ y.property)⟩, ?_⟩
    apply Subtype.ext
    change Q.J (-Q.J (y : V)) = y
    rw [map_neg, Q.J_sq]
    simp

/-- The restricted `J` isometry of an invariant submodule. -/
noncomputable def restrictJ (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hJ : ∀ ⦃x : V⦄, x ∈ W → Q.J x ∈ W) : W ≃ₗᵢ[ℝ] W :=
  LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective (restrictJLinear Q W hJ) (restrictJLinear_bijective Q W hJ))
    (fun x => by
      change ‖Q.J (x : V)‖ = ‖(x : V)‖
      exact Q.J.norm_map _)

/-- The quaternionic structure induced on a submodule invariant under `I` and `J`. -/
noncomputable def restrict (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hI : ∀ ⦃x : V⦄, x ∈ W → Q.I x ∈ W)
    (hJ : ∀ ⦃x : V⦄, x ∈ W → Q.J x ∈ W) : QuaternionicStructure W where
  I := restrictI Q W hI
  J := restrictJ Q W hJ
  I_sq := by
    intro x
    apply Subtype.ext
    exact Q.I_sq x
  J_sq := by
    intro x
    apply Subtype.ext
    exact Q.J_sq x
  I_J_anti := by
    intro x
    apply Subtype.ext
    exact Q.I_J_anti x

@[simp] theorem coe_restrictI_apply (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hI : ∀ ⦃x : V⦄, x ∈ W → Q.I x ∈ W) (x : W) :
    (restrictI Q W hI x : V) = Q.I x := rfl

@[simp] theorem coe_restrictJ_apply (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hJ : ∀ ⦃x : V⦄, x ∈ W → Q.J x ∈ W) (x : W) :
    (restrictJ Q W hJ x : V) = Q.J x := rfl

@[simp] theorem coe_restrict_I_apply (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hI : ∀ ⦃x : V⦄, x ∈ W → Q.I x ∈ W)
    (hJ : ∀ ⦃x : V⦄, x ∈ W → Q.J x ∈ W) (x : W) :
    ((restrict Q W hI hJ).I x : V) = Q.I x := rfl

@[simp] theorem coe_restrict_J_apply (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hI : ∀ ⦃x : V⦄, x ∈ W → Q.I x ∈ W)
    (hJ : ∀ ⦃x : V⦄, x ∈ W → Q.J x ∈ W) (x : W) :
    ((restrict Q W hI hJ).J x : V) = Q.J x := rfl

@[simp] theorem coe_restrict_K_apply (Q : QuaternionicStructure V) (W : Submodule ℝ V)
    (hI : ∀ ⦃x : V⦄, x ∈ W → Q.I x ∈ W)
    (hJ : ∀ ⦃x : V⦄, x ∈ W → Q.J x ∈ W) (x : W) :
    ((restrict Q W hI hJ).K x : V) = Q.K x := by
  rw [K_apply, K_apply, coe_restrict_I_apply, coe_restrict_J_apply]

/-- Restrict an endomorphism that preserves a submodule. -/
def restrictEndomorphism (A : V →ₗ[ℝ] V) (W : Submodule ℝ V)
    (hA : ∀ ⦃x : V⦄, x ∈ W → A x ∈ W) : W →ₗ[ℝ] W where
  toFun x := ⟨A x, hA x.property⟩
  map_add' x y := by
    ext
    exact A.map_add x y
  map_smul' r x := by
    ext
    exact A.map_smul r x

@[simp] theorem coe_restrictEndomorphism_apply (A : V →ₗ[ℝ] V) (W : Submodule ℝ V)
    (hA : ∀ ⦃x : V⦄, x ∈ W → A x ∈ W) (x : W) :
    (restrictEndomorphism A W hA x : V) = A x := rfl

theorem restrictEndomorphism_mem_skewCentralizer (Q : QuaternionicStructure V)
    (W : Submodule ℝ V)
    (hI : ∀ ⦃x : V⦄, x ∈ W → Q.I x ∈ W)
    (hJ : ∀ ⦃x : V⦄, x ∈ W → Q.J x ∈ W)
    (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer)
    (hAW : ∀ ⦃x : V⦄, x ∈ W → A x ∈ W) :
    restrictEndomorphism A W hAW ∈ (restrict Q W hI hJ).skewCentralizer := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simpa using hA.1 (x : V) (y : V)
  · intro x
    apply Subtype.ext
    simpa using hA.2.1 (x : V)
  · intro x
    apply Subtype.ext
    simpa using hA.2.2 (x : V)

end
end QuaternionicStructure
end QuaternionicSymmetry
