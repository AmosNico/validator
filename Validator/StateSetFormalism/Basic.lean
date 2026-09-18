module

public import Strips.VarSet

/-! # Basic definitions for formulas
This file provides definitions and lemmas for
models, literals, clauses, cubes, CNF-formulas and DNF-formulas.
-/

namespace Validator

public section

open STRIPS (VarSet)

/-! ## Model -/

/--
`Model` is usually in the in the context of a formula, where it represents a model of this formula,
i.e. an assignment of variables making the formula true.
It is used to show the correctness of operations.
-/
abbrev Model n := Fin n → Prop

/-- A set of models. -/
abbrev Models n := Set (Model n)

/-! ## Literal -/

/--
A Literal is a variable `i` (represented by `(i, true)`) or
its negation (represented by `(i, false)`).
-/
@[unbox]
structure Literal (n : ℕ) where
  var : Fin n
  isPos : Bool
deriving DecidableEq

namespace Literal

def models {n} : Literal n → Models n
  | ⟨i, true⟩ => { M | M i }
  | ⟨i, false⟩ => { M | ¬M i }

lemma mem_models {n} (l : Literal n) M : M ∈ l.models ↔ (M l.var ↔ l.isPos) := by
  simp [models]
  split
  all_goals simp

@[expose]
def negate {n} (l : Literal n) : Literal n :=
  ⟨l.var, !l.isPos⟩

@[simp]
lemma models_negate {n} (l : Literal n) : l.negate.models = l.modelsᶜ := by
  simp only [models, negate]
  grind only [= Set.mem_compl_iff, usr Set.mem_ofPred_eq]

lemma eq_or_eq_negate_iff_var_eq {n} {l l' : Literal n} :
    l.var = l'.var ↔ l = l' ∨ l = l'.negate := by
  rcases l with ⟨v, b⟩
  rcases l' with ⟨v', b'⟩
  have := Bool.eq_or_eq_not b b'
  grind only [negate]

end Literal

/-! ## Clause -/

/-- A clause is a disjuction of literals. -/
abbrev Clause n := List (Literal n)

namespace Clause

def models {n} (γ : Clause n) : Models n :=
  { M | ∃ l ∈ γ, M ∈ l.models }

@[simp]
lemma mem_models {n} (γ : Clause n) M : M ∈ γ.models ↔ ∃ l ∈ γ, M ∈ l.models := by
  simp [models]

@[simp]
lemma models_nil {n} : models ([] : Clause n) = ∅ := by
  simp only [models, List.not_mem_nil, false_and, exists_false, Set.ofPred_false]

@[simp]
lemma models_append {n} (γ1 γ2 : Clause n) : models (γ1 ++ γ2) = γ1.models ∪ γ2.models := by
  ext M
  grind only [models, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]

def vars {n} (γ : Clause n) : VarSet n :=
  VarSet.ofList (γ.map Literal.var)

@[simp]
lemma mem_vars {n} (γ : Clause n) {i} : i ∈ γ.vars ↔ ∃ l ∈ γ, l.var = i := by
  simp only [vars, VarSet.mem_ofList, List.mem_map]

@[simp]
lemma vars_cons {n} (γ : Clause n) {l} : Clause.vars (l :: γ) = γ.vars.insert l.var := by
  rw [SetLike.ext_iff]
  grind only [vars, VarSet.mem_insert, List.map_cons, VarSet.mem_ofList, List.mem_cons]

end Clause

/-! ## Cube -/

/-- A cube is a conjunction of literals. -/
abbrev Cube n := List (Literal n)

namespace Cube

def models {n} (δ : Cube n) : Models n :=
  { M | ∀ l ∈ δ, M ∈ l.models }

@[simp]
lemma mem_models {n} (δ : Cube n) M : M ∈ δ.models ↔ ∀ l ∈ δ, M ∈ l.models := by
  simp [models]

@[simp]
lemma models_append {n} (δ1 δ2 : Cube n) : models (δ1 ++ δ2) = δ1.models ∩ δ2.models := by
  ext M
  grind only [models, List.mem_append, Set.mem_ofPred_eq, Set.mem_inter_iff]

@[simp]
lemma models_nil {n} : models ([] : Cube n) = Set.univ := by
  simp only [models, List.not_mem_nil, IsEmpty.forall_iff, implies_true, Set.ofPred_true]

@[simp]
lemma models_cons {n l} (δ : Cube n) : models (l :: δ) = l.models ∩ δ.models := by
  ext M
  simp only [models, List.mem_cons, forall_eq_or_imp, Set.mem_ofPred_eq, Set.mem_inter_iff]

def vars {n} (δ : Cube n) : VarSet n :=
  VarSet.ofList (δ.map Literal.var)

@[simp]
lemma mem_vars {n} (δ : Cube n) i : i ∈ δ.vars ↔ ∃ l ∈ δ, i = l.var := by
  grind only [vars, Literal, VarSet.mem_ofList, List.mem_map]

@[simp]
lemma vars_cons {n} (δ : Cube n) {l} : Cube.vars (l :: δ) = δ.vars.insert l.var := by
  rw [SetLike.ext_iff]
  grind only [vars, VarSet.mem_insert, List.map_cons, VarSet.mem_ofList, List.mem_cons]

-- TODO : remove
lemma vars_append {n} (δ δ' : Cube n) : Cube.vars (δ ++ δ') = δ.vars ∪ δ'.vars := by
  rw [SetLike.ext_iff]
  grind only [vars, VarSet.mem_union, VarSet.mem_ofList, = List.map_append, = List.mem_append]

def consistent {n} (δ : Cube n) : Bool :=
  δ.all fun l ↦ l.negate ∉ δ

lemma consistent_iff {n} {δ : Cube n} : δ.consistent ↔ δ.models ≠ ∅ := by
  simp only [consistent, decide_not, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, ne_eq, Set.ext_iff, mem_models, Set.mem_empty_iff_false, iff_false,
    not_forall, not_exists, not_not, Literal.mem_models]
  constructor
  · intro h1
    use fun i ↦ ⟨i, true⟩ ∈ δ
    rintro ⟨v, b⟩ h2
    grind only [Literal.negate]
  · rintro ⟨M, h1⟩ l h2 h3
    have h4 := h1 l.negate h3
    simp only [Literal.negate] at h4
    grind only

end Cube

/-- The negation of a clause -/
def Clause.neg {n} (γ : Clause n) : Cube n :=
  γ.map Literal.negate

lemma Clause.models_neg {n} {γ : Clause n} : γ.neg.models = γ.modelsᶜ := by
  simp [neg, Cube.models, Clause.models, compl]

/-- The negation of a cube -/
def Cube.neg {n} (δ : Cube n) : Clause n :=
  δ.map Literal.negate

lemma Cube.models_neg {n} {δ : Cube n} : δ.neg.models = δ.modelsᶜ := by
  simp [neg, Cube.models, Clause.models, compl]

/-! ## CNF -/

/-- A CNF-formula is a conjunction of clauses. -/
abbrev CNF n := List (Clause n)

namespace CNF

def models {n} (φ : CNF n) : Models n :=
  { M | ∀ γ ∈ φ, M ∈ γ.models }

@[simp]
lemma mem_models {n} (φ : CNF n) {M} : M ∈ φ.models ↔ ∀ γ ∈ φ, M ∈ γ.models := by
  simp [models]

@[simp]
lemma models_nil {n} : CNF.models ([] : CNF n) = Set.univ := by
  simp only [models, List.not_mem_nil, IsEmpty.forall_iff, implies_true, Set.ofPred_true]

@[simp]
lemma models_cons {n} (φ : CNF n) {γ} : CNF.models (γ :: φ) = γ.models ∩ φ.models := by
  simp only [models, List.mem_cons, Clause.models, Set.mem_ofPred_eq, forall_eq_or_imp,
    Set.inter_def]

@[simp]
lemma models_append {n} (φ ψ : CNF n) : (φ ++ ψ).models = φ.models ∩ ψ.models := by
  ext M
  simp
  grind

lemma models_mem_empty {n} (φ : CNF n) (h : [] ∈ φ) : φ.models = ∅ := by
  grind only [mem_models, = Set.mem_empty_iff_false, Clause.mem_models, ← List.not_mem_nil]

def vars {n} (φ : CNF n) : VarSet n :=
  φ.foldr (fun γ V ↦ V ∪ γ.vars) ∅

@[simp]
lemma mem_vars {n} (φ : CNF n) {i} : i ∈ φ.vars ↔ ∃ γ ∈ φ, i ∈ γ.vars := by
  induction φ with
  | nil => grind only [vars, List.foldr_nil, VarSet.mem_empty, List.not_mem_nil]
  | cons γ φ ih =>
    grind only [vars, Clause.mem_vars, List.foldr_cons, VarSet.mem_union, List.mem_cons]

@[simp]
lemma vars_cons {n γ} {φ : CNF n} : CNF.vars (γ :: φ) = γ.vars ∪ φ.vars := by
  simp only [SetLike.ext_iff, mem_vars, List.mem_cons, Clause.mem_vars, exists_eq_or_imp,
    VarSet.mem_union, implies_true]

@[simp]
lemma forall_iff_subset_models {n} {φ : CNF n} {Ms} : (∀ γ ∈ φ, Ms ⊆ γ.models) ↔ Ms ⊆ φ.models := by
  grind only [Set.subset_def, Clause.mem_models, models, Set.mem_ofPred_eq]

lemma models_equiv_right {n} {φ : CNF n} {M M' : Model n} :
    (∀ i ∈ vars φ, M i = M' i) → M ∈ models φ → M' ∈ models φ := by
  simp [Literal.mem_models]
  grind

end CNF

/-! ## DNF -/

/-- A DNF-formula is a conjunction of cubes. -/
abbrev DNF n := List (Cube n)

def DNF.models {n} (φ : DNF n) : Models n :=
  { M |  ∃ δ ∈ φ, M ∈ δ.models }

@[simp]
lemma DNF.mem_models {n} (φ : DNF n) {M} : M ∈ φ.models ↔ ∃ δ ∈ φ, M ∈ δ.models := by
  simp [models]

@[simp]
lemma DNF.exists_iff_models_subset {n} {φ : DNF n} {Ms} :
    (∀ δ ∈ φ, δ.models ⊆ Ms) ↔ φ.models ⊆ Ms := by
  grind only [Set.subset_def, Cube.mem_models, models, Set.mem_ofPred_eq]
