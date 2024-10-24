/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Elab
import HepLean.Tensors.ComplexLorentz.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HepLean.Tensors.Tree.NodeIdentities.Basic
import HepLean.Tensors.Tree.NodeIdentities.PermProd
import HepLean.Tensors.Tree.NodeIdentities.PermContr
import HepLean.Tensors.Tree.NodeIdentities.ProdComm
import HepLean.Tensors.Tree.NodeIdentities.ContrSwap
import HepLean.Tensors.Tree.NodeIdentities.ContrContr
import HepLean.Tensors.ComplexLorentz.Basis
import LLMLean
/-!

## Lemmas related to complex Lorentz tensors.

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open TensorTree
open OverColor.Discrete
noncomputable section

namespace Fermion

set_option maxRecDepth 20000 in
lemma contr_rank_2_symm {T1 : (Lorentz.complexContr ⊗ Lorentz.complexContr).V}
    {T2 : (Lorentz.complexCo ⊗ Lorentz.complexCo).V} :
    {T1 | μ ν ⊗ T2 | μ ν = T2 | μ ν ⊗ T1 | μ ν}ᵀ := by
  rw [perm_tensor_eq (contr_tensor_eq (contr_tensor_eq (prod_comm _ _ _ _)))]
  rw [perm_tensor_eq (contr_tensor_eq (perm_contr _ _))]
  rw [perm_tensor_eq (perm_contr _ _)]
  rw [perm_perm]
  rw [perm_eq_id]
  · rw [(contr_tensor_eq (contr_swap _ _))]
    rw [perm_contr]
    rw [perm_tensor_eq (contr_swap _ _)]
    rw [perm_perm]
    rw [perm_eq_id]
    · rfl
    · rfl
  · apply OverColor.Hom.ext
    ext x
    exact Fin.elim0 x

lemma contr_rank_2_symm' {T1 : (Lorentz.complexCo ⊗ Lorentz.complexCo).V}
    {T2 : (Lorentz.complexContr ⊗ Lorentz.complexContr).V} :
    {T1 | μ ν ⊗ T2 | μ ν = T2 | μ ν ⊗ T1 | μ ν}ᵀ := by
  rw [perm_tensor_eq contr_rank_2_symm]
  rw [perm_perm]
  rw [perm_eq_id]
  apply OverColor.Hom.ext
  ext x
  exact Fin.elim0 x

set_option maxRecDepth 20000 in
/-- Contracting a rank-2 anti-symmetric tensor with a rank-2 symmetric tensor gives zero. -/
lemma antiSymm_contr_symm {A : (Lorentz.complexContr ⊗ Lorentz.complexContr).V}
    {S : (Lorentz.complexCo ⊗ Lorentz.complexCo).V}
    (hA : {A | μ ν = - (A | ν μ)}ᵀ) (hs : {S | μ ν = S | ν μ}ᵀ) :
    {A | μ ν ⊗ S | μ ν}ᵀ.tensor = 0 := by
  have h1 {M : Type} [AddCommGroup M] [Module ℂ M] {x : M} (h : x = - x) : x = 0 := by
    rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ x] at h
    simpa using h
  refine h1 ?_
  rw [← neg_tensor]
  rw [neg_perm] at hA
  nth_rewrite 1 [contr_tensor_eq (contr_tensor_eq (prod_tensor_eq_fst hA))]
  nth_rewrite 1 [(contr_tensor_eq (contr_tensor_eq (prod_tensor_eq_snd hs)))]
  rw [contr_tensor_eq (contr_tensor_eq (neg_fst_prod _ _))]
  rw [contr_tensor_eq (neg_contr _)]
  rw [neg_contr]
  rw [neg_tensor]
  apply congrArg
  rw [contr_tensor_eq (contr_tensor_eq (prod_perm_left _ _ _ _))]
  rw [contr_tensor_eq (perm_contr _ _)]
  rw [perm_contr]
  rw [perm_tensor_eq (contr_tensor_eq (contr_tensor_eq (prod_perm_right _ _ _ _)))]
  rw [perm_tensor_eq (contr_tensor_eq (perm_contr _ _))]
  rw [perm_tensor_eq (perm_contr _ _)]
  rw [perm_perm]
  nth_rewrite 1 [perm_tensor_eq (contr_contr _ _ _)]
  rw [perm_perm]
  rw [perm_eq_id]
  · rfl
  · rfl

lemma symm_contr_antiSymm {S : (Lorentz.complexCo ⊗ Lorentz.complexCo).V}
    {A : (Lorentz.complexContr ⊗ Lorentz.complexContr).V}
    (hA : {A | μ ν = - (A | ν μ)}ᵀ) (hs : {S | μ ν = S | ν μ}ᵀ) :
    {S | μ ν ⊗ A | μ ν}ᵀ.tensor = 0 := by
  rw [contr_rank_2_symm', perm_tensor, antiSymm_contr_symm hA hs]
  rfl

lemma antiSymm_add_self {A : (Lorentz.complexContr ⊗ Lorentz.complexContr).V}
    (hA : {A | μ ν = - (A | ν μ)}ᵀ) :
    {A | μ ν + A | ν μ}ᵀ.tensor = 0 := by
  rw [← TensorTree.add_neg (twoNodeE complexLorentzTensor Color.up Color.up A)]
  apply TensorTree.add_tensor_eq_snd
  rw [neg_tensor_eq hA, neg_tensor_eq (neg_perm _ _), neg_neg]

/-!

## The contraction of Pauli matrices with Pauli matrices

And related results.

-/
open complexLorentzTensor

def leftMetricMulRightMap := (Sum.elim ![Color.upL, Color.upL] ![Color.upR, Color.upR]) ∘ finSumFinEquiv.symm

lemma leftMetric_mul_rightMetric : {Fermion.leftMetric | α α' ⊗ Fermion.rightMetric | β β'}ᵀ.tensor
    = basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    - basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)
    - basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0) := by
  rw [prod_tensor_eq_fst (leftMetric_expand_tree)]
  rw [prod_tensor_eq_snd (rightMetric_expand_tree)]
  rw [prod_add_both]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_tensor_eq <| prod_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_eq_one _ _ (by simp)]
  rw [add_tensor_eq_fst <| add_tensor_eq_snd <| smul_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| prod_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_snd <| smul_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| prod_basisVector_tree _ _]
  rw [← add_assoc]
  simp only [add_tensor, smul_tensor, tensorNode_tensor]
  change _ =  basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    +- basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)
    +- basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0)
  congr 1
  congr 1
  congr 1
  all_goals
    congr
    funext x
    fin_cases x <;> rfl

def pauliMatrixLowerMap := ((Sum.elim ![Color.down, Color.down] ![Color.up, Color.upL, Color.upR] ∘ ⇑finSumFinEquiv.symm) ∘
    Fin.succAbove 0 ∘ Fin.succAbove 1)

abbrev pauliMatrixContrMap {n : ℕ} (c : Fin n → complexLorentzTensor.C) := (Sum.elim c ![Color.up, Color.upL, Color.upR] ∘ ⇑finSumFinEquiv.symm)

lemma prod_pauliMatrix_basis_tree_expand {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (t : TensorTree complexLorentzTensor c) :
    (TensorTree.prod t (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)).tensor = (((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 0 | 1 => 0 | 2 => 0)))).add
    (((t.prod (tensorNode
       (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 0 | 1 => 1 | 2 => 1)))).add
    (((t.prod (tensorNode
       (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 1 | 1 => 0 | 2 => 1)))).add
    (((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 1 | 1 => 1 | 2 => 0)))).add
   ((TensorTree.smul (-I) ((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 2 | 1 => 0 | 2 => 1))))).add
    ((TensorTree.smul I ((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 2 | 1 => 1 | 2 => 0))))).add
    ((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 3 | 1 => 0 | 2 => 0))).add
    (TensorTree.smul (-1) (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR]
        fun | 0 => 3 | 1 => 1 | 2 => 1))))))))))).tensor := by
  rw [prod_tensor_eq_snd <| pauliMatrix_basis_expand_tree]
  rw [prod_add _ _ _]
  rw [add_tensor_eq_snd <|  prod_add _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| prod_add _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| prod_add _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    prod_add _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| prod_add _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd  <| prod_add _ _ _]
  /- Moving smuls. -/
  rw [add_tensor_eq_snd  <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_fst <| prod_smul _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| prod_smul _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd  <| add_tensor_eq_snd<| add_tensor_eq_snd
    <| add_tensor_eq_snd <| prod_smul _ _ _]
  rfl


lemma contr_pauliMatrix_basis_tree_expand {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (t : TensorTree complexLorentzTensor c) (i : Fin (n + 3)) (j : Fin (n +2))
    (h : (pauliMatrixContrMap c) (i.succAbove j) = complexLorentzTensor.τ ((pauliMatrixContrMap c) i)) :
    (contr i j h (TensorTree.prod t (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor))).tensor =
    ((contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 0 | 1 => 0 | 2 => 0)))).add
    ((contr i j h (t.prod (tensorNode
       (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 0 | 1 => 1 | 2 => 1)))).add
    ((contr i j h (t.prod (tensorNode
       (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 1 | 1 => 0 | 2 => 1)))).add
    ((contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 1 | 1 => 1 | 2 => 0)))).add
   ((TensorTree.smul (-I) (contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 2 | 1 => 0 | 2 => 1))))).add
    ((TensorTree.smul I (contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 2 | 1 => 1 | 2 => 0))))).add
    ((contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 3 | 1 => 0 | 2 => 0)))).add
    (TensorTree.smul (-1) (contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 3 | 1 => 1 | 2 => 1)))))))))))).tensor := by
  rw [contr_tensor_eq <| prod_pauliMatrix_basis_tree_expand _]
  /- Moving contr over add. -/
  rw [contr_add]
  rw [add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  /- Moving contr over smul. -/
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    contr_smul _ _]

lemma basis_contr_pauliMatrix_basis_tree_expand' {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (i : Fin (n + 3)) (j : Fin (n +2))
    (h : (pauliMatrixContrMap c) (i.succAbove j) = complexLorentzTensor.τ ((pauliMatrixContrMap c) i))
    (b :  Π k, Fin (complexLorentzTensor.repDim (c k))) :
    let c' := Sum.elim c ![Color.up, Color.upL, Color.upR] ∘ finSumFinEquiv.symm
    let b' (i1 i2 i3 : Fin 4) := fun i => prodBasisVecEquiv (finSumFinEquiv.symm i)
      ((HepLean.PiTensorProduct.elimPureTensor b (fun | 0 => i1 | 1 => i2 | 2 => i3)) (finSumFinEquiv.symm i))
    (contr i j h (TensorTree.prod (tensorNode (basisVector c b)) (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor))).tensor = ((contr i j h ((tensorNode
    (basisVector c' (b' 0 0 0))))).add
    ((contr i j h ((tensorNode (basisVector c' (b' 0 1 1))))).add
    ((contr i j h ((tensorNode (basisVector c' (b' 1 0 1))))).add
    ((contr i j h ((tensorNode (basisVector c' (b' 1 1 0))))).add
    ((TensorTree.smul (-I) (contr i j h ((tensorNode (basisVector c' (b' 2 0 1)))))).add
    ((TensorTree.smul I (contr i j h ((tensorNode (basisVector c' (b' 2 1 0)))))).add
    ((contr i j h ((tensorNode (basisVector c' (b' 3 0 0))))).add
    (TensorTree.smul (-1) (contr i j h ((tensorNode
      (basisVector c' (b' 3 1 1))))))))))))).tensor := by
  rw [contr_pauliMatrix_basis_tree_expand]
  /- Product of basis vectors . -/
  rw [add_tensor_eq_fst <| contr_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| contr_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_tensor_eq
    <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst
    <| contr_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_fst <| smul_tensor_eq <| contr_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| contr_tensor_eq
      <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_tensor_eq
    <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|  add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| smul_tensor_eq
    <| contr_tensor_eq <| prod_basisVector_tree _ _]
  rfl

lemma basis_contr_pauliMatrix_basis_tree_expand {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (i : Fin (n + 3)) (j : Fin (n +2))
    (h : (pauliMatrixContrMap c) (i.succAbove j) = complexLorentzTensor.τ ((pauliMatrixContrMap c) i))
    (b :  Π k, Fin (complexLorentzTensor.repDim (c k))) :
    let c' := (Sum.elim c ![Color.up, Color.upL, Color.upR] ∘ finSumFinEquiv.symm)
      ∘ Fin.succAbove i ∘ Fin.succAbove j
    let b'' (i1 i2 i3 : Fin 4) : (i : Fin (n + (Nat.succ 0).succ.succ)) →
        Fin (complexLorentzTensor.repDim (Sum.elim c ![Color.up, Color.upL, Color.upR] (finSumFinEquiv.symm i))) := fun i => prodBasisVecEquiv (finSumFinEquiv.symm i)
      ((HepLean.PiTensorProduct.elimPureTensor b (fun | (0 : Fin 3) => i1 | 1 => i2 | 2 => i3)) (finSumFinEquiv.symm i))
    let b' (i1 i2 i3 : Fin 4) := fun k => (b'' i1 i2 i3) (i.succAbove (j.succAbove k))
    (contr i j h (TensorTree.prod (tensorNode (basisVector c b))
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor))).tensor = (((
    TensorTree.smul (contrBasisVectorMul i j (b'' 0 0 0)) (tensorNode (basisVector c' (b' 0 0 0))))).add
    (((TensorTree.smul (contrBasisVectorMul i j (b'' 0 1 1)) (tensorNode (basisVector c' (b' 0 1 1))))).add
    (((TensorTree.smul (contrBasisVectorMul i j (b'' 1 0 1)) (tensorNode (basisVector c' (b' 1 0 1))))).add
    (((TensorTree.smul (contrBasisVectorMul i j (b'' 1 1 0)) (tensorNode (basisVector c' (b' 1 1 0))))).add
    ((TensorTree.smul (-I) ((TensorTree.smul (contrBasisVectorMul i j (b'' 2 0 1)) (tensorNode (basisVector c' (b' 2 0 1)))))).add
    ((TensorTree.smul I ((TensorTree.smul (contrBasisVectorMul i j (b'' 2 1 0)) (tensorNode (basisVector c' (b' 2 1 0)))))).add
    (((TensorTree.smul (contrBasisVectorMul i j (b'' 3 0 0)) (tensorNode (basisVector c' (b' 3 0 0))))).add
    (TensorTree.smul (-1) ((TensorTree.smul (contrBasisVectorMul i j (b'' 3 1 1)) (tensorNode
      (basisVector c' (b' 3 1 1))))))))))))).tensor := by
  rw [basis_contr_pauliMatrix_basis_tree_expand']
  /- Contracting basis vectors. -/
  rw [add_tensor_eq_fst <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst
    <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_fst <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq
    <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
     add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
     smul_tensor_eq <| contr_basisVector_tree _]

lemma pauliMatrix_contr_down_0 :
    (contr 0 1 rfl (((tensorNode (basisVector ![Color.down, Color.down] fun x => 0)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor
    = basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 1 | 2 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [one_smul, zero_smul, smul_zero, add_zero]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_down_0_tree :
     (contr 0 1 rfl (((tensorNode (basisVector ![Color.down, Color.down] fun x => 0)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor
    = (TensorTree.add (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 0 | 2 => 0)))
    (tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 1 | 2 => 1)))).tensor := by
  exact pauliMatrix_contr_down_0

lemma pauliMatrix_contr_down_1 : (contr 0 1 rfl
    (((tensorNode (basisVector ![Color.down, Color.down] fun x => 1)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor
    = basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 0 | 2 => 1)
    + basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 1 | 2 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_down_1_tree : (contr 0 1 rfl
    (((tensorNode (basisVector ![Color.down, Color.down] fun x => 1)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor
    = (TensorTree.add (tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 0 | 2 => 1)))
    (tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 1 | 2 => 0)))).tensor := by
  exact pauliMatrix_contr_down_1

lemma pauliMatrix_contr_down_2 : (contr 0 1 rfl
    (((tensorNode (basisVector ![Color.down, Color.down] fun x => 2)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor
    = (- I) • basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 0 | 2 => 1)
    + (I) •  basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 1 | 2 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 2
    funext k
    fin_cases k <;> rfl
  · congr 2
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_down_2_tree : (contr 0 1 rfl
    (((tensorNode (basisVector ![Color.down, Color.down] fun x => 2)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor =
    (TensorTree.add
    (smul (- I) (tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 0 | 2 => 1))))
    (smul I (tensorNode (basisVector
      pauliMatrixLowerMap (fun | 0 => 2 | 1 => 1 | 2 => 0))))).tensor := by
  exact pauliMatrix_contr_down_2

lemma pauliMatrix_contr_down_3 : (contr 0 1 rfl
    (((tensorNode (basisVector ![Color.down, Color.down] fun x => 3)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor
    =  basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 0 | 2 => 0)
    + (- 1 : ℂ) • basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 2
    funext k
    fin_cases k <;> rfl
  · congr 2
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_down_3_tree : (contr 0 1 rfl
    (((tensorNode (basisVector ![Color.down, Color.down] fun x => 3)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor =
    (TensorTree.add
      ((tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 0 | 2 => 0))))
      (smul (-1)  (tensorNode (basisVector pauliMatrixLowerMap
      (fun | 0 => 3 | 1 => 1 | 2 => 1))))).tensor := by
  exact pauliMatrix_contr_down_3

def pauliMatrixContrPauliMatrixMap := ((Sum.elim
        ((Sum.elim ![Color.down, Color.down] ![Color.up, Color.upL, Color.upR] ∘ ⇑finSumFinEquiv.symm) ∘
          Fin.succAbove 0 ∘ Fin.succAbove 1)
        ![Color.up, Color.upL, Color.upR] ∘
      ⇑finSumFinEquiv.symm) ∘
    Fin.succAbove 0 ∘ Fin.succAbove 2)

lemma pauliMatrix_contr_lower_0_0_0 :  (contr 0 2 rfl
    (((tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 0 | 2 => 0))).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor)))).tensor = basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0)
    + basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_0_1_1 : (contr 0 2 rfl
    (((tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 1 | 2 => 1))).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor)))).tensor = basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0)
    + basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_1_0_1 : (contr 0 2 rfl
    (((tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 0 | 2 => 1))).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor)))).tensor = basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    + basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_1_1_0 : (contr 0 2 rfl
    (((tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 1 | 2 => 0))).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor)))).tensor = basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_2_0_1 : (contr 0 2 rfl
    (((tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 0 | 2 => 1))).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor)))).tensor =
      (-I) • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    + (I) • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 2
    funext k
    fin_cases k <;> rfl
  · congr 2
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_2_1_0 : (contr 0 2 rfl
    (((tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 1 | 2 => 0))).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor)))).tensor =
      (-I) • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + (I) • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 2
    funext k
    fin_cases k <;> rfl
  · congr 2
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_3_0_0 : (contr 0 2 rfl
    (((tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 0 | 2 => 0))).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor)))).tensor =
      basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0)
      + (-1 : ℂ) • basisVector pauliMatrixContrPauliMatrixMap
      (fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 2
    funext k
    fin_cases k <;> rfl
  · congr 2
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_3_1_1 : (contr 0 2 rfl
    (((tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 1 | 2 => 1))).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor)))).tensor =
     basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0)
    + (-1 : ℂ) • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 2
    funext k
    fin_cases k <;> rfl
  · congr 2
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_lower : {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β}ᵀ.tensor
    = basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 1 | 2 => 1)
    - basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 0 | 2 => 1)
    - basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 1 | 2 => 0)
    + I • basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 0 | 2 => 1)
    - I • basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 1 | 2 => 0)
    - basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 0 | 2 => 0)
    + basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  rw [contr_tensor_eq <| prod_tensor_eq_fst <| coMetric_basis_expand_tree]
  /- Moving the prod through additions. -/
  rw [contr_tensor_eq <| add_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_prod _ _ _]
  /- Moving the prod through smuls. -/
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst
    <| smul_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| smul_prod _ _ _]
  /- Moving contraction through addition. -/
  rw [contr_add]
  rw [add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  /- Moving contraction through smul. -/
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_smul _ _]
  /- Replacing the contractions. -/
  rw [add_tensor_eq_fst <| pauliMatrix_contr_down_0_tree]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| pauliMatrix_contr_down_1_tree]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| pauliMatrix_contr_down_2_tree]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| smul_tensor_eq <| pauliMatrix_contr_down_3_tree]
  /- Simplifying -/
  simp only [add_tensor, smul_tensor, tensorNode_tensor, smul_add,_root_.smul_smul]
  simp only [Nat.reduceAdd, Fin.isValue, neg_smul, one_smul, mul_neg, neg_mul, one_mul,
    _root_.neg_neg, mul_one]
  rfl

lemma pauliMatrix_lower_tree : {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β}ᵀ.tensor
    = (TensorTree.add (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 0 | 2 => 0))) <|
    TensorTree.add (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 1 | 2 => 1))) <|
    TensorTree.add (TensorTree.smul (-1) (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 0 | 2 => 1)))) <|
    TensorTree.add (TensorTree.smul (-1) (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 1 | 2 => 0)))) <|
    TensorTree.add (TensorTree.smul I (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 0 | 2 => 1)))) <|
    TensorTree.add (TensorTree.smul (-I) (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 1 | 2 => 0)))) <|
    TensorTree.add (TensorTree.smul (-1) (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 0 | 2 => 0)))) <|
      (tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 1 | 2 => 1)))).tensor := by
  rw [pauliMatrix_lower]
  simp only [Nat.reduceAdd, Fin.isValue, add_tensor,
    tensorNode_tensor, smul_tensor, neg_smul, one_smul]
  rfl

lemma pauliMatrix_contract_pauliMatrix_aux :
  {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β ⊗ PauliMatrix.asConsTensor | ν α' β'}ᵀ.tensor
  = ((tensorNode
      ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0) +
        basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1)).add
    ((tensorNode
      ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0) +
      basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1)).add
    ((TensorTree.smul (-1) (tensorNode
      ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1) +
      basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0))).add
    ((TensorTree.smul (-1) (tensorNode
      ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1) +
      basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0))).add
    ((TensorTree.smul I (tensorNode
      ((-I • basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1) +
        I • basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0))).add
    ((TensorTree.smul (-I) (tensorNode
      ((-I • basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1) +
      I • basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0))).add
      ((TensorTree.smul (-1) (tensorNode
        ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0) +
        (-1 : ℂ) • basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1))).add
      (tensorNode
        ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0) +
        (-1 : ℂ) • basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1))))))))).tensor := by
  rw [contr_tensor_eq <| prod_tensor_eq_fst <| pauliMatrix_lower_tree]
  /- Moving the prod through additions. -/
  rw [contr_tensor_eq <| add_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_prod _ _ _]
  /- Moving the prod through smuls. -/
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_prod _ _ _]
  /- Moving contraction through addition. -/
  rw [contr_add]
  rw [add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  /- Moving contraction through smul. -/
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  /- Replacing the contractions. -/
  rw [add_tensor_eq_fst <| eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_0_0_0]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_0_1_1]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_1_0_1]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_1_1_0]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_2_0_1]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_2_1_0]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_3_0_0]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_3_1_1]

lemma pauliMatrix_contract_pauliMatrix :
  {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β ⊗ PauliMatrix.asConsTensor | ν α' β'}ᵀ.tensor =
  2 • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1)
    + 2 • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0)
    - 2 • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)
    - 2 • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1) := by
  rw [pauliMatrix_contract_pauliMatrix_aux]
  simp only [Nat.reduceAdd, Fin.isValue, Fin.succAbove_zero, neg_smul,
    one_smul, add_tensor, tensorNode_tensor, smul_tensor, smul_add, smul_neg, _root_.smul_smul,
    neg_mul, _root_.neg_neg]
  ring_nf
  rw [Complex.I_sq]
  simp only [ neg_smul, one_smul, _root_.neg_neg]
  abel

end Fermion

end
