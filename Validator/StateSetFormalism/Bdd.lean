module

public import Validator.StateSetFormalism.Formula
/-
Cannot compile inline/specializing declaration `instConsistency` as it uses
`BDD.instDecidableSemanticEquiv` of module `Bdd.BDD` which must be imported publicly.
This limitation may be lifted in the future.
-/
public import Bdd.BDD

namespace Validator
open Formula

public structure BDD n where
  private vars : VarSet n
  private bdd : _root_.BDD
  private nvars_prop : bdd.nvars = n
  private vars_prop : ∀ i : Fin n, bdd.DependsOn i  → i ∈ vars

namespace Formula.Model

noncomputable def toVector {n} (M : Model n) : Vector Bool n :=
  have := Classical.decPred M
  Vector.ofFn fun i ↦ if M i then true else false

def ofVector {n} (V : Vector Bool n) : Model n :=
  fun i ↦ V[i]

@[simp]
lemma ofVector_toVector {n} (M : Model n) : ofVector M.toVector = M := by
  simp [ofVector, toVector, funext_iff]

@[simp]
lemma toVector_ofVector {n} (V : Vector Bool n) : (ofVector V).toVector = V := by
  simp [ofVector, toVector]

end Formula.Model
namespace BDD

lemma nvars_prop_max {n} {φ ψ : BDD n} : max φ.bdd.nvars ψ.bdd.nvars = n :=
  by simp only [φ.nvars_prop, ψ.nvars_prop, max_self]

def models {n} (φ : BDD n) : Models n :=
  { M | φ.bdd[M.toVector]'(le_of_eq φ.nvars_prop) }

def top_bdd (n : ℕ) : _root_.BDD :=
  (BDD.const true).lift (BDD.const_nvars ▸ n.zero_le)

lemma getElem_top_bdd {n n'} {V : Vector Bool n'} {h} :
    (top_bdd n)[V]'h = true := by
  simp only [top_bdd, BDD.getElem_lift, BDD.getElem_const]

lemma dependsOn_top_bdd {n} : ∀ i, ¬(top_bdd n).DependsOn i := by
  simp only [top_bdd, BDD.lift_dependsOn, BDD.const_dependsOn, not_false_eq_true, implies_true]

def bot_bdd (n : ℕ) : _root_.BDD :=
  (BDD.const false).lift (BDD.const_nvars ▸ n.zero_le)

lemma getElem_bot_bdd {n} {V : Vector Bool n} {h} :
    (bot_bdd n)[V]'h = false := by
  simp only [bot_bdd, BDD.getElem_lift, BDD.getElem_const]

lemma dependsOn_bot_bdd {n} : ∀ i, ¬(bot_bdd n).DependsOn i := by
  simp only [bot_bdd, BDD.lift_dependsOn, BDD.const_dependsOn, not_false_eq_true, implies_true]

def not {n} (φ : BDD n) : BDD n where
  vars := φ.vars
  bdd := φ.bdd.not
  nvars_prop := by simp only [BDD.not_nvars, φ.nvars_prop]
  vars_prop := by
    grind only [φ.vars_prop, BDD.not_dependsOn]

@[simp]
lemma models_not {n} (φ : BDD n) : φ.not.models = φ.modelsᶜ := by
  simp only [models, not, BDD.getElem_not, Bool.not_eq_eq_eq_not, Bool.not_true, Set.compl_def,
    Set.mem_setOf_eq, Bool.not_eq_true]

def ofLiteral {n} : Literal n → _root_.BDD
  | ⟨i, true⟩ => BDD.var i
  | ⟨i, false⟩ => (BDD.var i).not

lemma nvars_ofLiteral {n} (l : Literal n) : (ofLiteral l).nvars ≤ n := by
  simp [ofLiteral]
  grind only [!BDD.var_nvars, !BDD.not_nvars]

lemma getElem_ofLiteral {n n'} (l : Literal n) {h} (h' : n' = n) {V : Vector Bool n'} :
    (ofLiteral l)[V]'h = decide (Model.ofVector (V.cast h') l.1 = l.2) := by
  simp only [ofLiteral, Model.ofVector, Fin.getElem_fin, Vector.getElem_cast, eq_iff_iff,
    Bool.coe_iff_coe]
  grind only [BDD.getElem_var, BDD.getElem_not, Bool.decide_eq_false]

@[simp]
lemma dependsOn_ofLiteral {n} {l : Literal n} {i} : (ofLiteral l).DependsOn i ↔ i = l.var := by
  simp only [ofLiteral]
  grind only [BDD.var_dependsOn, BDD.not_dependsOn]

abbrev ofCube_bdd {n} (δ : Cube n) : _root_.BDD :=
  δ.foldr (fun l φ ↦ φ.and (ofLiteral l)) (top_bdd n)

lemma nvars_ofCube_bdd {n} (δ : Cube n) : (ofCube_bdd δ).nvars = n := by
  induction δ with
  | nil => simp only [List.foldr_nil, BDD.lift_nvars, top_bdd]
  | cons l δ ih => simp only [List.foldr_cons, BDD.and_nvars, ih, sup_eq_left, nvars_ofLiteral]

lemma getElem_ofCube_bdd {n} (δ : Cube n) {h} v :
    (ofCube_bdd δ)[v]'h = δ.all fun l ↦ Model.ofVector v l.1 = l.2 := by
  induction δ with
  | nil => simp only [List.foldr_nil, getElem_top_bdd, eq_iff_iff, List.all_nil]
  | cons l δ ih =>
    simp only [List.foldr_cons, BDD.getElem_and, eq_iff_iff, List.all_cons]
    rw [getElem_ofLiteral l rfl]
    grind only [Model.ofVector, Fin.getElem_fin, Vector.getElem_cast]

def ofCube {n} (δ : Cube n) : BDD n where
  vars := δ.vars
  bdd := ofCube_bdd δ
  nvars_prop := nvars_ofCube_bdd δ
  vars_prop := by
    induction δ with
    | nil => simp [dependsOn_top_bdd]
    | cons l δ ih =>
      intro i h1
      simp only [ofCube_bdd, List.foldr_cons, Cube.vars_cons, VarSet.mem_insert] at *
      apply BDD.and_dependsOn at h1
      grind only [dependsOn_ofLiteral]

@[simp]
lemma vars_ofCube {n} (δ : Cube n) : (ofCube δ).vars = δ.vars := by
  simp only [ofCube]

@[simp]
lemma models_ofCube {n} (δ : Cube n) : (ofCube δ).models = δ.models := by
  simp only [models, ofCube, Set.ext_iff, Set.mem_setOf_eq, Cube.mem_models]
  induction δ with
  | nil => simp [getElem_top_bdd]
  | cons l δ ih =>
    simp only [List.foldr_cons, BDD.getElem_and, getElem_ofLiteral, Vector.cast_rfl,
      Model.ofVector_toVector, eq_iff_iff, Bool.and_eq_true, ih, Literal.mem_models,
      decide_eq_true_eq, List.mem_cons, forall_eq_or_imp]
    grind only

abbrev ofClause_bdd {n} (γ : Clause n) : _root_.BDD :=
  γ.foldr (fun l φ ↦ φ.or (ofLiteral l)) (bot_bdd n)

lemma nvars_ofClause_bdd {n} (γ : Clause n) : (ofClause_bdd γ).nvars = n := by
  induction γ with
  | nil => simp only [List.foldr_nil, BDD.lift_nvars, bot_bdd]
  | cons l γ ih => simp only [List.foldr_cons, BDD.or_nvars, ih, sup_eq_left, nvars_ofLiteral]

lemma getElem_ofClause_bdd {n} (γ : Clause n) {h} v :
    (ofClause_bdd γ)[v]'h = γ.any fun l ↦ Model.ofVector v l.1 = l.2 := by
  induction γ with
  | nil => simp only [List.foldr_nil, getElem_bot_bdd, eq_iff_iff, List.any_nil]
  | cons l δ ih =>
    simp only [List.foldr_cons, BDD.getElem_or, eq_iff_iff, List.any_cons]
    rw [getElem_ofLiteral l rfl]
    grind only [Model.ofVector, Fin.getElem_fin, Vector.getElem_cast]

def ofClause {n} (γ : Clause n) : BDD n where
  vars := γ.vars
  bdd := ofClause_bdd γ
  nvars_prop := nvars_ofClause_bdd γ
  vars_prop := by
    induction γ with
    | nil => simp [dependsOn_bot_bdd]
    | cons l δ ih =>
      intro i h1
      simp only [ofClause_bdd, List.foldr_cons, Clause.vars_cons, VarSet.mem_insert] at *
      apply BDD.or_dependsOn at h1
      grind only [dependsOn_ofLiteral]

@[simp]
lemma models_ofClause {n} (γ : Clause n) : (ofClause γ).models = γ.models := by
  simp only [models, ofClause, Set.ext_iff, Set.mem_setOf_eq, Clause.mem_models]
  induction γ with
  | nil => simp [getElem_bot_bdd]
  | cons l δ ih =>
    simp only [List.foldr_cons, BDD.getElem_or, getElem_ofLiteral, Vector.cast_rfl,
      Model.ofVector_toVector, eq_iff_iff, Bool.or_eq_true, ih, Literal.mem_models,
      decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    grind only

@[no_expose]
public instance {n} : Formula n (BDD n) where

  vars φ := φ.vars

  models := models

  models_equiv_right φ M M' h1 h2 := by
    have h3 := φ.nvars_prop
    suffices
      φ.bdd[M.toVector] = φ.bdd[M'.toVector] by
      simp_all only [eq_iff_iff, models, Set.mem_setOf_eq]
    apply BDD.congrInterpretation
    rintro ⟨i, h4⟩ h5
    simp [Model.toVector]
    have := φ.vars_prop ⟨i, by omega⟩ h5
    grind only

@[no_expose]
public instance {n} : Top n (BDD n) where

  top := {
    vars := ∅
    bdd := top_bdd n
    nvars_prop := by
      simp only [top_bdd, BDD.lift_nvars]
    vars_prop := by
      simp only [dependsOn_top_bdd, VarSet.mem_empty, imp_self, implies_true]
  }

  models_top := by
    simp only [Formula.models, models, getElem_top_bdd, Set.setOf_true]

@[no_expose]
public instance {n} : Bot n (BDD n) where

  bot := {
    vars := ∅
    bdd := bot_bdd n
    nvars_prop := by
      simp only [bot_bdd, BDD.lift_nvars]
    vars_prop := by
      simp only [dependsOn_bot_bdd, VarSet.mem_empty, imp_self, implies_true]
  }

  vars_bot := by simp only [Formula.vars]

  models_bot := by
    simp only [Formula.models, models, getElem_bot_bdd, Bool.false_eq_true, Set.setOf_false]

@[no_expose]
public instance {n} : Consistency n (BDD n) where

  consistent φ := ¬φ.bdd.SemanticEquiv (BDD.const false)

  consistent_iff φ := by
    simp only [BDD.SemanticEquiv, BDD.getElem_const, not_forall, Bool.not_eq_false,
      decide_eq_true_eq, Set.Nonempty, Formula.models, models, Set.mem_setOf_eq]
    have h1 : max φ.bdd.nvars (BDD.const false).nvars = n := by
        simp only [φ.nvars_prop, BDD.const_nvars, Nat.zero_le, sup_of_le_left]
    constructor
    · rintro ⟨V, h2⟩
      use Model.ofVector (V.cast h1)
      simp only [Model.toVector_ofVector, BDD.const_nvars, Nat.zero_le, sup_of_le_left, Std.le_refl,
        BDD.getElem_cast, h2]
    · rintro ⟨M, h2⟩
      use M.toVector.cast h1.symm
      rw [BDD.getElem_cast h1.symm (hn := by omega)]
      exact h2

@[no_expose]
public instance {n} : BoundedConjuction n (BDD n) where

  and φ ψ := {
    vars := φ.vars ∪ ψ.vars
    bdd := φ.bdd.and ψ.bdd
    nvars_prop := by
      simp only [BDD.and_nvars, φ.nvars_prop, ψ.nvars_prop, max_self]
    vars_prop := by
      have := φ.vars_prop
      have := ψ.vars_prop
      grind only [VarSet.mem_union, BDD.and_dependsOn, φ.nvars_prop, ψ.nvars_prop]
  }

  models_and φ ψ := by
    simp only [Formula.models, models, BDD.getElem_and, Bool.and_eq_true, Set.ext_iff,
      Set.mem_setOf_eq, Set.mem_inter_iff, implies_true]

@[no_expose]
public instance {n} : BoundedDisjunction n (BDD n) where

  or φ ψ := {
    vars := φ.vars ∪ ψ.vars
    bdd := φ.bdd.or ψ.bdd
    nvars_prop := by
      simp only [BDD.or_nvars, φ.nvars_prop, ψ.nvars_prop, max_self]
    vars_prop := by
      have := φ.vars_prop
      have := ψ.vars_prop
      grind only [VarSet.mem_union, BDD.or_dependsOn, φ.nvars_prop, ψ.nvars_prop]
  }

  models_or φ ψ := by
    simp only [Formula.models, models, BDD.getElem_or, Bool.or_eq_true, Set.ext_iff,
      Set.mem_setOf_eq, Set.mem_union, implies_true]

@[no_expose]
public instance {n} : SententialEntailment n (BDD n) where

  entails φ ψ := ¬instConsistency.consistent (instBoundedConjuction.and φ ψ.not)

  entails_iff φ ψ := by
    simp only [BoundedConjuction.models_and, Consistency.consistent_iff, decide_not,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    simp only [Set.Nonempty, Formula.models, models_not, Set.mem_inter_iff, Set.mem_compl_iff,
      not_exists, not_and, not_not]
    grind only [= Set.subset_def]

@[no_expose]
public instance {n} : ClausalEntailment n (BDD n) where

  entails φ γ := instSententialEntailment.entails φ (ofClause γ)

  entails_iff φ γ := by
    simp only [SententialEntailment.entails_iff, Formula.models, models_ofClause]

@[no_expose]
public instance {n} : Implicant n (BDD n) where

  entails δ φ := instSententialEntailment.entails (ofCube δ) φ

  entails_iff δ φ := by
    simp only [SententialEntailment.entails_iff, Formula.models, models_ofCube]

@[no_expose]
public instance {n} : OfPartialModel n (BDD n) where

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

@[no_expose]
public instance {n} : Rename n (BDD n) where

  rename φ V r h1 := {
    vars := VarSet.rename r φ.vars
    bdd := by
      apply φ.bdd.relabel (φ.nvars_prop ▸ r.rename)
      rcases φ with ⟨vars, bdd, rfl, h2⟩
      simp only
      intro i i' h3 h4 h5
      have hi := h2 i h3
      have hi' := h2 i' h4
      have h4 := r.mono
      simp only [StrictMonoOn, SetLike.mem_coe] at h4
      simp only [Formula.vars] at h1
      specialize h4 (h1 i hi) (h1 i' hi') (by rw [Fin.lt_def]; grind only)
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
    simp [Formula.models, models, BDD.getElem_relabel, Model.toVector]
    congr

end Validator.BDD
