/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.Group.Basic
import HepLean.Lorentz.RealVector.Basic
import Mathlib.RepresentationTheory.Basic
import HepLean.Lorentz.Group.Restricted
import HepLean.Lorentz.PauliMatrices.SelfAdjoint
import HepLean.Meta.Informal
/-!
# The group SL(2, ℂ) and it's relation to the Lorentz group

The aim of this file is to give the relationship between `SL(2, ℂ)` and the Lorentz group.

-/
namespace Lorentz

open Matrix
open MatrixGroups
open Complex

namespace SL2C

noncomputable section

local instance : OfNat (Fin 1 ⊕ Fin 3) 0 where ofNat := .inl 0
local instance : OfNat (Fin 1 ⊕ Fin 3) 1 where ofNat := .inr 0
local instance : OfNat (Fin 1 ⊕ Fin 3) 2 where ofNat := .inr 1
local instance : OfNat (Fin 1 ⊕ Fin 3) 3 where ofNat := .inr 2
local notation "ℂ²ˣ²" => Matrix (Fin 2) (Fin 2) ℂ
local postfix:arg "²" => (· ^ 2)
open PauliMatrix (σSA σSAL σSAL' σ0 σ1 σ2 σ3)

/-!

## Some basic properties about SL(2, ℂ)

Possibly to be moved to mathlib at some point.
-/

lemma inverse_coe (M : SL(2, ℂ)) : M.1⁻¹ = (M⁻¹).1 := by
  apply Matrix.inv_inj
  simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true,
    nonsing_inv_nonsing_inv, SpecialLinearGroup.coe_inv]
  have h1 : IsUnit M.1.det := by
    simp
  rw [Matrix.inv_adjugate M.1 h1]
  · simp
  · simp

lemma transpose_coe (M : SL(2, ℂ)) : M.1ᵀ = (M.transpose).1 := rfl
/-!

## Representation of SL(2, ℂ) on spacetime

Through the correspondence between spacetime and self-adjoint matrices,
we can define a representation of `SL(2, ℂ)` on spacetime.

-/

/-- Given an element `M ∈ SL(2, ℂ)` the linear map from `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` to
  itself defined by `A ↦ M * A * Mᴴ`. -/
@[simps!]
def toSelfAdjointMap (M : SL(2, ℂ)) : selfAdjoint ℂ²ˣ² →ₗ[ℝ] selfAdjoint ℂ²ˣ² where
  toFun A := ⟨M.1 * A.1 * Mᴴ, .conjugate A.2 _⟩
  map_add' A B :=
    -- let lhs : selfAdjoint ℂ²ˣ² := {
    --   val := M.1 * (A.1 + B.1) * Mᴴ
    --   property := .conjugate (.add A.2 B.2) _
    -- }
    -- let rhs : selfAdjoint ℂ²ˣ² := {
    --   val := M.1 * A.1 * M.1ᴴ + M.1 * B.1 * M.1ᴴ
    --   property := .add (.conjugate A.2 _) (.conjugate B.2 _)
    -- }
    -- show lhs = rhs from
    suffices M.1 * (A.1 + B.1) * Mᴴ = M.1 * A.1 * Mᴴ + M.1 * B.1 * Mᴴ from Subtype.ext this
    by noncomm_ring
  map_smul' r A :=
    -- let lhs : selfAdjoint ℂ²ˣ² := {
    --   val := M.1 * (r • A.1) * M.1ᴴ
    --   property := .conjugate (SMul.smul r A).2 _
    -- }
    -- let rhs : selfAdjoint ℂ²ˣ² := SMul.smul r ⟨M.1 * A.1 * M.1ᴴ, .conjugate A.2 _⟩
    -- show lhs = rhs from
    suffices M.1 * (r • A.1) * Mᴴ = r • (M.1 * A.1 * Mᴴ) from Subtype.ext this
    by noncomm_ring

lemma toSelfAdjointMap_apply_det (M : SL(2, ℂ)) (A : selfAdjoint ℂ²ˣ²) :
    det ((toSelfAdjointMap M) A).1 = det A.1 :=
  calc  (M.1 * A.1 * Mᴴ).det
    _ = M.1.det * A.1.det * star M.1.det := by rw [det_mul, det_mul, det_conjTranspose]
    _ = 1 * A.1.det * 1 := by rw [M.2, star_one]
    _ = A.1.det := by rw [one_mul, mul_one]

lemma toSelfAdjointMap_apply_σSAL_inl (M : SL(2, ℂ)) :
    toSelfAdjointMap M (σSAL 0)
    = ((‖M 0 0‖² + ‖M 0 1‖² + ‖M 1 0‖² + ‖M 1 1‖²) / 2) • σSAL 0
    + (- ((M 0 1).re * (M 1 1).re + (M 0 1).im * (M 1 1).im
      + (M 0 0).im * (M 1 0).im + (M 0 0).re * (M 1 0).re)) • σSAL 1
    + (- (M 0 0).re * (M 1 0).im + (M 1 0).re * (M 0 0).im
      - (M 0 1).re * (M 1 1).im + (M 0 1).im * (M 1 1).re) • σSAL 2
    + ((- ‖M 0 0‖² - ‖M 0 1‖² + ‖M 1 0‖² + ‖M 1 1‖²) / 2) • σSAL 3 := by
  simp only [toSelfAdjointMap, σSAL, Fin.isValue, Basis.coe_mk, σSAL',
    σ0, LinearMap.coe_mk, AddHom.coe_mk, norm_eq_abs, neg_add_rev, σ1,
    neg_of, neg_cons, neg_zero, neg_empty, neg_mul, σ2, neg_neg, σ3]
  ext1
  simp only [Fin.isValue, AddSubgroup.coe_add, selfAdjoint.val_smul, smul_of, smul_cons, real_smul,
    ofReal_div, ofReal_add, ofReal_pow, ofReal_ofNat, mul_one, smul_zero, smul_empty, smul_neg,
    ofReal_neg, ofReal_mul, neg_add_rev, neg_neg, of_add_of, add_cons, head_cons, add_zero,
    tail_cons, zero_add, empty_add_empty, ofReal_sub]
  conv => lhs; erw [← eta_fin_two 1, mul_one]
  conv => lhs; lhs; rw [eta_fin_two M.1]
  conv => lhs; rhs; rw [eta_fin_two M.1ᴴ]
  simp only [Fin.isValue, conjTranspose_apply, RCLike.star_def, cons_mul, Nat.succ_eq_add_one,
    Nat.reduceAdd, vecMul_cons, head_cons, smul_cons, smul_eq_mul, smul_empty, tail_cons,
    empty_vecMul, add_zero, add_cons, empty_add_empty, empty_mul, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rw [mul_conj', mul_conj', mul_conj', mul_conj']
  ext x y
  match x, y with
  | 0, 0 =>
    simp only [Fin.isValue, norm_eq_abs, cons_val', cons_val_zero, empty_val', cons_val_fin_one]
    ring_nf
  | 0, 1 =>
    simp only [Fin.isValue, norm_eq_abs, cons_val', cons_val_one, head_cons, empty_val',
      cons_val_fin_one, cons_val_zero]
    ring_nf
    rw [← re_add_im (M 0 0), ← re_add_im (M 0 1), ← re_add_im (M 1 0), ← re_add_im (M 1 1)]
    simp only [Fin.isValue, map_add, conj_ofReal, _root_.map_mul, conj_I, mul_neg, add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im,
      mul_im, zero_add]
    ring_nf
    simp only [Fin.isValue, I_sq, mul_neg, mul_one, neg_mul, neg_neg, one_mul, sub_neg_eq_add]
    ring
  | 1, 0 =>
    simp only [Fin.isValue, norm_eq_abs, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
      cons_val_one, head_fin_const]
    ring_nf
    rw [← re_add_im (M 0 0), ← re_add_im (M 0 1), ← re_add_im (M 1 0), ← re_add_im (M 1 1)]
    simp only [Fin.isValue, map_add, conj_ofReal, _root_.map_mul, conj_I, mul_neg, add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im,
      mul_im, zero_add]
    ring_nf
    simp only [Fin.isValue, I_sq, mul_neg, mul_one, neg_mul, neg_neg, one_mul, sub_neg_eq_add]
    ring
  | 1, 1 =>
    simp only [Fin.isValue, norm_eq_abs, cons_val', cons_val_one, head_cons, empty_val',
      cons_val_fin_one, head_fin_const]
    ring_nf

theorem toSelfAdjointMap_one : toSelfAdjointMap 1 = 1 :=
  LinearMap.ext fun A => show toSelfAdjointMap 1 A = A from
  Subtype.ext <| show 1 * A.1 * 1ᴴ = A.1 from by simp

theorem toSelfAdjointMap_mul {M N : SL(2, ℂ)} :
    toSelfAdjointMap (M * N) = (toSelfAdjointMap M * toSelfAdjointMap N) :=
  LinearMap.ext fun A => show toSelfAdjointMap (M * N) A = (toSelfAdjointMap M * toSelfAdjointMap N) A from
  Subtype.ext <| show (M * N).1 * A.1 * (M * N)ᴴ = M.1 * (N.1 * A.1 * Nᴴ) * Mᴴ from by simp ; noncomm_ring

/-- The monoid homomorphisms from `SL(2, ℂ)` to matrices indexed by `Fin 1 ⊕ Fin 3`
  formed by the action `M A Mᴴ`. -/
def toMatrix : SL(2, ℂ) →* Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ where
  toFun M := LinearMap.toMatrix σSAL σSAL (toSelfAdjointMap M)
  map_one' :=
    calc  LinearMap.toMatrix _ _ (toSelfAdjointMap 1)
      _ = LinearMap.toMatrix _ _ 1 := congrArg _ toSelfAdjointMap_one
      _ = 1 := LinearMap.toMatrix_one ..
  map_mul' M N :=
    calc  LinearMap.toMatrix _ _ (toSelfAdjointMap (M * N))
      _ = LinearMap.toMatrix _ _ (toSelfAdjointMap M * toSelfAdjointMap N) := congrArg _ toSelfAdjointMap_mul
      _ = LinearMap.toMatrix _ _ (toSelfAdjointMap M) * LinearMap.toMatrix _ _ (toSelfAdjointMap N) := LinearMap.toMatrix_mul ..

lemma toMatrix_apply_contrMod (M : SL(2, ℂ)) (v : ContrMod 3) :
    toMatrix M *ᵥ v = ContrMod.toSelfAdjoint.symm (toSelfAdjointMap M (ContrMod.toSelfAdjoint v)) :=
  have ⟨w, (hv : ContrMod.toSelfAdjoint.symm w = v)⟩ := ContrMod.toSelfAdjoint.symm.surjective v
  have hw :=
    calc  ContrMod.toSelfAdjoint v
      _ = ContrMod.toSelfAdjoint (ContrMod.toSelfAdjoint.symm w) := congrArg _ hv.symm
      _ = w := LinearEquiv.apply_symm_apply ..
  let M' := toSelfAdjointMap M
  calc  toMatrix M *ᵥ v
    _ = toMatrix M *ᵥ ContrMod.toSelfAdjoint.symm w := congrArg _ hv.symm
    _ = toMatrix M *ᵥ ContrMod.toFin1dℝEquiv.symm (σSAL.repr w) := rfl
    _ = ContrMod.toFin1dℝEquiv.symm (toMatrix M *ᵥ σSAL.repr w) := rfl
    _ = ContrMod.toFin1dℝEquiv.symm (σSAL.repr (M' w)) := congrArg _ (LinearMap.toMatrix_mulVec_repr ..)
    _ = ContrMod.toSelfAdjoint.symm (M' w) := rfl
    _ = ContrMod.toSelfAdjoint.symm (M' (ContrMod.toSelfAdjoint v)) := congrArg _ (congr_arg _ hw.symm)

lemma toMatrix_mem_lorentzGroup (M : SL(2, ℂ)) : toMatrix M ∈ LorentzGroup 3 :=
  LorentzGroup.mem_iff_norm.mpr fun w : Contr 3 => ofReal_injective <|
  let Λ := toMatrix M
  let M' := toSelfAdjointMap M
  let w' := ContrMod.toSelfAdjoint w
  have h :=
    calc  ContrMod.toSelfAdjoint (Λ *ᵥ w)
      _ = ContrMod.toSelfAdjoint (ContrMod.toSelfAdjoint.symm (M' w')) := congrArg _ (toMatrix_apply_contrMod ..)
      _ = M' w' := LinearEquiv.apply_symm_apply ..
  calc  ↑⟪Λ *ᵥ w, Λ *ᵥ w⟫ₘ
    _ = (ContrMod.toSelfAdjoint (Λ *ᵥ w)).1.det := contrContrContractField.same_eq_det_toSelfAdjoint ..
    _ = (M' w').1.det := congrArg (·.1.det) h
    _ = w'.1.det := toSelfAdjointMap_apply_det ..
    _ = ↑⟪w, w⟫ₘ := symm <| contrContrContractField.same_eq_det_toSelfAdjoint ..

/-- The group homomorphism from `SL(2, ℂ)` to the Lorentz group `𝓛`. -/
@[simps!]
def toLorentzGroup : SL(2, ℂ) →* LorentzGroup 3 where
  toFun M := ⟨toMatrix M, toMatrix_mem_lorentzGroup M⟩
  map_one' := Subtype.ext <|
    calc  toMatrix 1
      _ = LinearMap.toMatrix σSAL σSAL (toSelfAdjointMap 1) := rfl
      _ = LinearMap.toMatrix σSAL σSAL 1 := congrArg _ toSelfAdjointMap_one
      _ = 1 := LinearMap.toMatrix_one ..
  map_mul' M N := Subtype.ext <|
    calc  toMatrix (M * N)
      _ = toMatrix M * toMatrix N := map_mul ..

lemma toLorentzGroup_eq_σSAL (M : SL(2, ℂ)) :
    toLorentzGroup M = LinearMap.toMatrix σSAL σSAL (toSelfAdjointMap M) := rfl

lemma toSelfAdjointMap_basis (i : Fin 1 ⊕ Fin 3) :
    toSelfAdjointMap M (σSAL i) = ∑ j, (toLorentzGroup M).1 j i • σSAL j :=
  calc  toSelfAdjointMap M (σSAL i)
    _ = toLin σSAL σSAL (toLorentzGroup M) (σSAL i) := DFunLike.congr_fun (toLin_toMatrix ..).symm _
    _ = ∑ j, (toLorentzGroup M).1 j i • σSAL j := toLin_self ..
/-
lemma toSelfAdjointMap_σSA (i : Fin 1 ⊕ Fin 3) :
    toSelfAdjointMap M (σSA i) =
    ∑ j, (toLorentzGroup M⁻¹).1 i j • σSA j := by
  have h1 : (toLorentzGroup M⁻¹).1 = minkowskiMatrix.dual (toLorentzGroup M).1 := by
    simp
  simp only [h1]
  rw [PauliMatrix.σSA_minkowskiMetric_σSAL, _root_.map_smul]
  rw [toSelfAdjointMap_basis]
  rw [Finset.smul_sum]
  apply congrArg
  funext j
  rw [smul_smul, PauliMatrix.σSA_minkowskiMetric_σSAL, smul_smul]
  apply congrFun
  apply congrArg
  exact Eq.symm (minkowskiMatrix.dual_apply_minkowskiMatrix ((toLorentzGroup M).1) i j)

/-- The first column of the Lorentz matrix formed from an element of `SL(2, ℂ)`. -/
lemma toLorentzGroup_fst_col (M : SL(2, ℂ)) :
    ((toLorentzGroup M).1 · (.inl 0)) = fun
      | .inl 0 => (‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) / 2
      | .inr 0 => - ((M 0 1).re * (M 1 1).re + (M 0 1).im * (M 1 1).im +
        (M 0 0).im * (M 1 0).im + (M 0 0).re * (M 1 0).re)
      | .inr 1 => - (M 0 0).re * (M 1 0).im + (M 1 0).re * (M 0 0).im
        - (M 0 1).re * (M 1 1).im + (M 0 1).im * (M 1 1).re
      | .inr 2 => (- ‖M 0 0‖ ^ 2 - ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) / 2 := by
  let k : Fin 1 ⊕ Fin 3 → ℝ
    | .inl 0 => (‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) / 2
    | .inr 0 => - ((M 0 1).re * (M 1 1).re + (M 0 1).im * (M 1 1).im +
      (M 0 0).im * (M 1 0).im + (M 0 0).re * (M 1 0).re)
    | .inr 1 => - (M 0 0).re * (M 1 0).im + (M 1 0).re * (M 0 0).im
      - (M 0 1).re * (M 1 1).im + (M 0 1).im * (M 1 1).re
    | .inr 2 => (- ‖M 0 0‖ ^ 2 - ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) / 2
  change ((toLorentzGroup M).1 · (.inl 0)) = k
  have h1 : toSelfAdjointMap M (σSAL (.inl 0)) = ∑ μ, k μ • σSAL μ := by
    simp [Fin.sum_univ_three]
    rw [toSelfAdjointMap_apply_σSAL_inl]
    abel
  rw [toSelfAdjointMap_basis] at h1
  have h1x := sub_eq_zero_of_eq h1
  rw [← Finset.sum_sub_distrib] at h1x
  funext μ
  refine sub_eq_zero.mp ?_
  refine Fintype.linearIndependent_iff.mp σSAL.linearIndependent
    (fun x => ((toLorentzGroup M).1 x (.inl 0) - k x)) ?_ μ
  rw [← h1x]
  congr
  funext x
  exact sub_smul ((toLorentzGroup M).1 x (.inl 0)) (k x) (σSAL x)

/-- The first element of the image of `SL(2, ℂ)` in the Lorentz group. -/
lemma toLorentzGroup_inl_inl (M : SL(2, ℂ)) :
    (toLorentzGroup M).1 (.inl 0) (.inl 0) =
    ((‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) / 2) :=
  congrFun (toLorentzGroup_fst_col M) _

/-- The image of `SL(2, ℂ)` in the Lorentz group is orthochronous. -/
lemma toLorentzGroup_isOrthochronous (M : SL(2, ℂ)) :
    LorentzGroup.IsOrthochronous (toLorentzGroup M) := by
  rw [LorentzGroup.IsOrthochronous]
  rw [toLorentzGroup_inl_inl]
  apply div_nonneg
  · apply add_nonneg
    · apply add_nonneg
      · apply add_nonneg
        · exact sq_nonneg _
        · exact sq_nonneg _
      · exact sq_nonneg _
    · exact sq_nonneg _
  · exact zero_le_two

/-!

## Homomorphism to the restricted Lorentz group

The homomorphism `toLorentzGroup` restricts to a homomorphism to the restricted Lorentz group.
In this section we will define this homomorphism.

-/

#check LorentzGroup.det_eq_one_or_neg_one
/-- The determinant of the image of `SL(2, ℂ)` in the Lorentz group is one. -/
lemma toLorentzGroup_det_one (M : SL(2, ℂ)) : (toLorentzGroup M).1.det = 1 :=
  -- let ⟨Λ, hΛ⟩ := toLorentzGroup M
  -- have k := LinearMap.det_toMatrix σSAL (toSelfAdjointMap M)
  -- have r : LinearMap.det (toSelfAdjointMap M) = det (1 : Matrix (Fin 2) (Fin 2) ℝ) := sorry
  -- have g := toSelfAdjointMap_apply_det M 1
  -- toLorentzGroup_eq_σSAL M ▸ k
  calc  det (toLorentzGroup M).1
    _ = det (LinearMap.toMatrix σSAL σSAL (toSelfAdjointMap M)) := rfl
    _ = LinearMap.det (toSelfAdjointMap M) := LinearMap.det_toMatrix ..
    _ = 1 := sorry

informal_lemma toRestrictedLorentzGroup where
  math :≈ "The homomorphism from `SL(2, ℂ)` to the restricted Lorentz group."
  deps :≈ [``toLorentzGroup, ``toLorentzGroup_det_one, ``toLorentzGroup_isOrthochronous,
    ``LorentzGroup.Restricted]

/-! TODO: Define homomorphism from `SL(2, ℂ)` to the restricted Lorentz group. -/
end
end SL2C

end Lorentz
-/
