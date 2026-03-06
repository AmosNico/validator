import Validator.StateSetFormalism.Formula
import Bdd.BDD

namespace Validator
open Formula

structure BDD n where
  vars : VarSet n
  bdd : _root_.BDD
  nvars_prop : bdd.nvars = n
  vars_prop : ∀ i : Fin n, Nary.DependsOn (bdd.denotation (by simp [nvars_prop])) i  → i ∈ vars

namespace Formula.Model

noncomputable def toVector {n} (M : Model n) : Vector Bool n :=
  have := Classical.decPred M
  Vector.ofFn fun i ↦ if M i then true else false

def ofVector {n} (V : Vector Bool n) : Model n :=
  fun i ↦ V[i]

@[simp]
lemma ofVector_toVector {n} (M : Model n) : ofVector M.toVector = M :=
  by simp [ofVector, toVector, funext_iff]

@[simp]
lemma toVector_ofVector {n} (V : Vector Bool n) : (ofVector V).toVector = V :=
  by simp [ofVector, toVector, Vector.ext_iff]

end Formula.Model
namespace BDD

private lemma nvars_prop_max {n} {φ ψ : BDD n} : max φ.bdd.nvars ψ.bdd.nvars = n :=
  by simp only [φ.nvars_prop, ψ.nvars_prop, max_self]

def models {n} (φ : BDD n) : Models n :=
  { M | φ.bdd.denotation (le_of_eq φ.nvars_prop) M.toVector }

private def top_bdd (n : ℕ) : _root_.BDD :=
  (BDD.const true).lift n.zero_le

private lemma top_bdd_denotation {n n'} {V : Vector Bool n'} {h} :
  (top_bdd n).denotation h V = true :=
  by simp only [top_bdd, BDD.lift_denotation, BDD.const_denotation, Function.const_apply]

private def bot_bdd (n : ℕ) : _root_.BDD :=
  (BDD.const false).lift n.zero_le

private lemma bot_bdd_denotation {n} {V : Vector Bool n} {h} :
  (bot_bdd n).denotation h V = false :=
  by simp only [bot_bdd, BDD.lift_denotation, BDD.const_denotation, Function.const_apply]

def not {n} (φ : BDD n) : BDD n where
  vars := φ.vars
  bdd := φ.bdd.not
  nvars_prop := by simp only [BDD.not_nvars, φ.nvars_prop]
  vars_prop := by
    grind only [φ.vars_prop, !BDD.not_nvars, Nary.DependsOn, Nary.IndependentOf, BDD.not_denotation]

@[simp]
lemma models_not {n} (φ : BDD n) : φ.not.models = φ.modelsᶜ :=
  by simp only [models, not, BDD.not_denotation, Bool.not_eq_eq_eq_not, Bool.not_true,
    Set.compl_def, Set.mem_setOf_eq, Bool.not_eq_true]

private def ofLiteral {n} : Literal n → _root_.BDD
| (i, true) => BDD.var i
| (i, false) => (BDD.var i).not

private lemma nvars_ofLiteral {n} (l : Literal n) : (ofLiteral l).nvars ≤ n :=
  by
    simp [ofLiteral]
    grind only [!BDD.var_nvars, !BDD.not_nvars]

private lemma ofLiteral_denotation {n n'} (l : Literal n) {h} (h' : n' = n) {V : Vector Bool n'} :
  (ofLiteral l).denotation h V = decide (Model.ofVector (V.cast h') l.1 = l.2) :=
  by
    simp only [ofLiteral, Model.ofVector, Fin.getElem_fin, Vector.getElem_cast, eq_iff_iff,
      Bool.coe_iff_coe]
    grind only [BDD.var_denotation, BDD.not_denotation]

private abbrev ofCube_bdd {n} (δ : Cube n) : _root_.BDD :=
  δ.foldr (fun l φ ↦ φ.and (ofLiteral l)) (top_bdd n)

private lemma nvars_ofCube_bdd {n} (δ : Cube n) : (ofCube_bdd δ).nvars = n :=
  by
    induction δ with
    | nil => simp only [List.foldr_nil, BDD.lift_nvars, top_bdd]
    | cons l δ ih => simp only [List.foldr_cons, BDD.and_nvars, ih, sup_eq_left, nvars_ofLiteral]

private lemma denotation_ofCube_bdd {n} (δ : Cube n) {h} v :
  (ofCube_bdd δ).denotation h v = δ.all fun l ↦ Model.ofVector v l.1 = l.2 :=
  by
    induction δ with
    | nil => simp only [List.foldr_nil, top_bdd_denotation, eq_iff_iff, List.all_nil]
    | cons l δ ih =>
      simp only [List.foldr_cons, BDD.and_denotation, eq_iff_iff, List.all_cons]
      rw [ofLiteral_denotation l rfl]
      grind only [Model.ofVector, Fin.getElem_fin, Vector.getElem_cast]

def ofCube {n} (δ : Cube n) : BDD n where
  vars := δ.vars
  bdd := ofCube_bdd δ
  nvars_prop := nvars_ofCube_bdd δ
  vars_prop := by
    simp_all only [Nary.DependsOn, Nary.IndependentOf, Bool.forall_bool, not_and, Vector.set_set,
      implies_true, not_true_eq_false, imp_false, not_forall, Cube.mem_vars, forall_exists_index]
    rintro i v h1
    have h2 := le_of_eq (nvars_ofCube_bdd δ)
    cases h3 : (ofCube_bdd δ).denotation h2 v with
    | true =>
      simp only [denotation_ofCube_bdd δ, Model.ofVector, Fin.getElem_fin] at h1
      grind only [= Vector.getElem_set, List.all_eq_true]
    | false =>
      simp only [denotation_ofCube_bdd δ, Model.ofVector, Fin.getElem_fin] at h1
      grind only [= List.all_eq, = Vector.getElem_set]

@[simp]
lemma vars_ofCube {n} (δ : Cube n) : (ofCube δ).vars = δ.vars :=
  by simp only [ofCube]

@[simp]
lemma models_ofCube {n} (δ : Cube n) : (ofCube δ).models = δ.models :=
  by
    simp only [models, ofCube, Set.ext_iff, Set.mem_setOf_eq, Cube.mem_models]
    induction δ with
    | nil => simp [top_bdd_denotation]
    | cons l δ ih =>
      simp only [List.foldr_cons, BDD.and_denotation, ofLiteral_denotation, Vector.cast_rfl,
        Model.ofVector_toVector, eq_iff_iff, Bool.and_eq_true, ih, Literal.mem_models,
        decide_eq_true_eq, List.mem_cons, forall_eq_or_imp]
      grind only


private abbrev ofClause_bdd {n} (γ : Clause n) : _root_.BDD :=
  γ.foldr (fun l φ ↦ φ.or (ofLiteral l)) (bot_bdd n)

private lemma nvars_ofClause_bdd {n} (γ : Clause n) : (ofClause_bdd γ).nvars = n :=
  by
    induction γ with
    | nil => simp only [List.foldr_nil, BDD.lift_nvars, bot_bdd]
    | cons l γ ih => simp only [List.foldr_cons, BDD.or_nvars, ih, sup_eq_left, nvars_ofLiteral]

private lemma denotation_ofClause_bdd {n} (γ : Clause n) {h} v :
  (ofClause_bdd γ).denotation h v = γ.any fun l ↦ Model.ofVector v l.1 = l.2 :=
  by
    induction γ with
    | nil => simp only [List.foldr_nil, bot_bdd_denotation, eq_iff_iff, List.any_nil]
    | cons l δ ih =>
      simp only [List.foldr_cons, BDD.or_denotation, eq_iff_iff, List.any_cons]
      rw [ofLiteral_denotation l rfl]
      grind only [Model.ofVector, Fin.getElem_fin, Vector.getElem_cast]

def ofClause {n} (γ : Clause n) : BDD n where
  vars := γ.vars
  bdd := ofClause_bdd γ
  nvars_prop := nvars_ofClause_bdd γ
  vars_prop := by
    simp_all only [Nary.DependsOn, Nary.IndependentOf, Bool.forall_bool, not_and, Vector.set_set,
      implies_true, not_true_eq_false, imp_false, not_forall, Clause.mem_vars, forall_exists_index]
    rintro i v h1
    have h2 := le_of_eq (nvars_ofClause_bdd γ)
    cases h3 : (ofClause_bdd γ).denotation h2 v with
    | true =>
      simp only [denotation_ofClause_bdd γ, Model.ofVector, Fin.getElem_fin] at h1
      grind only [= Vector.getElem_set, List.any_eq_true]
    | false =>
      simp only [denotation_ofClause_bdd γ, Model.ofVector, Fin.getElem_fin] at h1
      grind only [= Vector.getElem_set, = List.any_eq]

@[simp]
lemma models_ofClause {n} (γ : Clause n) : (ofClause γ).models = γ.models :=
  by
    simp only [models, ofClause, Set.ext_iff, Set.mem_setOf_eq, Clause.mem_models]
    induction γ with
    | nil => simp [bot_bdd_denotation]
    | cons l δ ih =>
      simp only [List.foldr_cons, BDD.or_denotation, ofLiteral_denotation, Vector.cast_rfl,
        Model.ofVector_toVector, eq_iff_iff, Bool.or_eq_true, ih, Literal.mem_models,
        decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
      grind only

instance {n} : Formula n (BDD n) where

  vars φ := φ.vars

  models := models

  models_equiv_right φ M M' h1 h2 := by
    have h3 := φ.nvars_prop
    suffices
      φ.bdd.denotation (le_of_eq h3) M.toVector = φ.bdd.denotation (le_of_eq h3) M'.toVector by
      simp_all only [eq_iff_iff, models, Set.mem_setOf_eq]
    apply Nary.eq_of_forall_dependency_getElem_eq
    rintro ⟨i, h4⟩
    have h5 := φ.vars_prop i h4
    grind only [Model.toVector, = Fin.getElem_fin, = Vector.getElem_ofFn]

instance {n} : Top n (BDD n) where

  top := {
    vars := ∅
    bdd := top_bdd n
    nvars_prop := by simp only [top_bdd, BDD.lift_nvars]
    vars_prop := by simp [top_bdd]
  }

  models_top := by
    simp only [Formula.models, models, top_bdd_denotation, Set.setOf_true]

instance {n} : Bot n (BDD n) where

  bot := {
    vars := ∅
    bdd := bot_bdd n
    nvars_prop := by simp only [bot_bdd, BDD.lift_nvars]
    vars_prop := by simp [bot_bdd]
  }

  vars_bot := by simp only [Formula.vars]

  models_bot := by
    simp only [Formula.models, models, bot_bdd_denotation, Bool.false_eq_true, Set.setOf_false]

instance {n} : Consistency n (BDD n) where

  consistent φ := ¬φ.bdd.SemanticEquiv (BDD.const false)

  consistent_iff φ := by
    simp only [BDD.SemanticEquiv, BDD.const_nvars, BDD.const_denotation, funext_iff,
      Function.const_apply, not_forall, Bool.not_eq_false, decide_eq_true_eq, Set.Nonempty,
      Formula.models, models, Set.mem_setOf_eq]
    have h1 : max φ.bdd.nvars 0 = n := by
        simp only [φ.nvars_prop, zero_le, sup_of_le_left]
    constructor
    · rintro ⟨V, h2⟩
      use Model.ofVector (h1 ▸ V)
      grind only [Model.toVector_ofVector]
    · rintro ⟨M, h2⟩
      use h1.symm ▸ M.toVector
      grind only [Model.toVector_ofVector]

instance {n} : BoundedConjuction n (BDD n) where

  and φ ψ := {
    vars := φ.vars ∪ ψ.vars
    bdd := φ.bdd.and ψ.bdd
    nvars_prop := by
      simp only [BDD.and_nvars, φ.nvars_prop, ψ.nvars_prop, max_self]
    vars_prop := by
      have := φ.vars_prop
      have := ψ.vars_prop
      simp_all
      grind only [φ.nvars_prop, ψ.nvars_prop]

  }

  models_and φ ψ := by
    simp only [Formula.models, models, BDD.and_denotation, Bool.and_eq_true, Set.ext_iff,
      Set.mem_setOf_eq, Set.mem_inter_iff, implies_true]

instance {n} : BoundedDisjunction n (BDD n) where

  or φ ψ := {
    vars := φ.vars ∪ ψ.vars
    bdd := φ.bdd.or ψ.bdd
    nvars_prop := by
      simp only [BDD.or_nvars, φ.nvars_prop, ψ.nvars_prop, max_self]
    vars_prop := by
      have := φ.vars_prop
      have := ψ.vars_prop
      simp_all
      grind only [φ.nvars_prop, ψ.nvars_prop]
  }

  models_or φ ψ := by
    simp only [Formula.models, models, BDD.or_denotation, Bool.or_eq_true, Set.ext_iff,
      Set.mem_setOf_eq, Set.mem_union, implies_true]

instance {n} : SententialEntailment n (BDD n) where

  entails φ ψ := ¬instConsistency.consistent (instBoundedConjuction.and φ ψ.not)

  entails_iff φ ψ := by
    simp only [BoundedConjuction.models_and, Consistency.consistent_iff, decide_not,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    simp only [Set.Nonempty, Formula.models, models_not, Set.mem_inter_iff, Set.mem_compl_iff,
      not_exists, not_and, not_not]
    grind only [= Set.subset_def]

instance {n} : ClausalEntailment n (BDD n) where

  entails φ γ := instSententialEntailment.entails φ (ofClause γ)

  entails_iff φ γ := by
    simp only [SententialEntailment.entails_iff, Formula.models, models_ofClause]

instance {n} : Implicant n (BDD n) where

  entails δ φ := instSententialEntailment.entails (ofCube δ) φ

  entails_iff δ φ := by
    simp only [SententialEntailment.entails_iff, Formula.models, models_ofCube]

instance {n} : OfPartialModel n (BDD n) where

  ofPartialModel M := ofCube (M.toCube)

  vars_ofPartialModel M := by
    simp only [Formula.vars, vars_ofCube, PartialModel.vars_toCube]

  models_ofPartialModel M := by
    simp only [Formula.models, models_ofCube, PartialModel.models_toCube]

/-

private def rename_bdd {n} (φ : BDD n) (V : VarSet n) (r : Renaming V) (h1 : φ.vars ⊆ V) :
  _root_.BDD :=
  by
    apply φ.bdd.relabel (φ.nvars_prop ▸ r.rename)
    rcases φ with ⟨vars, bdd, rfl, h2⟩
    intro i i' h3
    have hi := h2 i.val i.prop
    have hi' := h2 i'.val i'.prop
    have h4 := r.mono
    simp only [StrictMonoOn, SetLike.mem_coe] at h4
    specialize h4 (h1 _ hi) (h1 _ hi') (by rw [Fin.lt_def]; grind only)
    grind only

private lemma nvars_rename_bdd {n} {φ : BDD n} {V r h1} : (rename_bdd φ V r h1).nvars = n := by
  simp only [rename_bdd, BDD.relabel_nvars, φ.nvars_prop]

private lemma denotation_rename_bdd {n} {φ : BDD n} {V r h1 h v} :
  (rename_bdd φ V r h1).denotation h v =
    φ.bdd.denotation (le_of_eq φ.nvars_prop) (Vector.ofFn (fun i ↦ v[r.rename i])) :=
  by
    rcases φ with ⟨vars, bdd, rfl, h2⟩
    simp [rename_bdd, BDD.relabel]

instance {n} : Rename n (BDD n) where

  rename φ V r h1 := {
    vars := VarSet.rename r φ.vars
    bdd := rename_bdd φ V r h1
    nvars_prop := nvars_rename_bdd
    vars_prop i h2 := by
      have h3 := φ.vars_prop i
      have : bdd.denotation = sorry := by sorry
      rw [(φ.bdd.relabel (φ.nvars_prop ▸ r.rename) sorry).relabel_denotation] at h2
      simp only [Nary.DependsOn, Nary.IndependentOf, Bool.forall_bool, not_and, not_forall] at h2 h3

      rw [BDD.relabel_denotation] at h2
      sorry
  }

  vars_rename φ V r h1 := by
    simp only [Formula.vars, VarSet.mem_rename, Set.mem_image, SetLike.mem_coe]
    grind only

  models_rename φ V r h1 := by
    rcases φ with ⟨vars, bdd, rfl, h2⟩
    ext M
    simp [rename_bdd, Formula.models, models, BDD.relabel, Model.toVector]
    congr
-/

instance {n} : Rename n (BDD n) where

  rename φ V r h1 := {
    vars := VarSet.rename r φ.vars
    bdd := by
      apply φ.bdd.relabel (φ.nvars_prop ▸ r.rename)
      rcases φ with ⟨vars, bdd, rfl, h2⟩
      intro i i' h3
      have hi := h2 i.val i.prop
      have hi' := h2 i'.val i'.prop
      have h4 := r.mono
      simp only [StrictMonoOn, SetLike.mem_coe] at h4
      simp only [Formula.vars] at h1
      specialize h4 (h1 _ hi) (h1 _ hi') (by rw [Fin.lt_def]; grind only)
      grind only
    nvars_prop := by
      simp only [BDD.relabel_nvars, φ.nvars_prop]
    vars_prop := by
      rcases φ with ⟨vars, bdd, rfl, h2⟩
      simp only [BDD.relabel_dependsOn]
      rintro i ⟨j, rfl, h3⟩
      specialize h2 j h3
      grind only [VarSet.mem_rename]
  }

  vars_rename φ V r h1 := by
    simp only [Formula.vars, VarSet.mem_rename, Set.mem_image, SetLike.mem_coe]
    grind only

  models_rename φ V r h1 := by
    rcases φ with ⟨vars, bdd, rfl, h2⟩
    ext M
    simp [Formula.models, models, BDD.relabel, Model.toVector]
    congr

end Validator.BDD
