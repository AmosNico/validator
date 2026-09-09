module

public import Validator.StateSetFormalism.Formula

namespace Validator
open Formula STRIPS

structure RawMODS n where
  private vars : VarSet n
  private mods : List (PartialModel n)
  private prop : ∀ M ∈ mods, M.vars = vars
deriving DecidableEq

public structure MODS n where
  private inner : RawMODS n
  /-- All variables in `vars` are needed for representing the formula. -/
  private reduced : ∀ i ∈ inner.vars, ∃ M ∈ inner.mods, ∀ M' ∈ inner.mods,
    (∀ l : Literal n, l.var ≠ i → l ∈ M ↔ l ∈ M') → M = M'
deriving DecidableEq

namespace Formula.PartialModel

/--
Returns the conjunction of two partial models.
Returns `none` if the conjunction of the two partial models is inconsistent.
-/
def and {n} (M1 M2 : PartialModel n) : Option (PartialModel n) :=
  let pos := M1.pos ∪ M2.pos
  let neg := M1.neg ∪ M2.neg
  if h : pos ∩ neg = ∅ then
    return ⟨pos, neg, h⟩
  else
    none

lemma vars_and {n} {M1 M2 M : PartialModel n} :
    M1.and M2 = some M → M.vars = M1.vars ∪ M2.vars := by
  simp only [and, Option.pure_def, Option.dite_none_right_eq_some, Option.some.injEq]
  rintro ⟨h1, rfl⟩
  simp only [vars_eq, SetLike.ext_iff, VarSet.mem_union]
  tauto

@[grind →]
lemma models_and {n} {M1 M2 M : PartialModel n} :
    M1.and M2 = some M → M.models = M1.models ∩ M2.models := by
  simp only [and, Option.pure_def, Option.dite_none_right_eq_some, Option.some.injEq]
  rintro ⟨h1, rfl⟩
  simp only [Set.ext_iff, mem_models', VarSet.mem_union, Set.mem_inter_iff]
  grind only

lemma isSome_and_iff {n} {M1 M2 : PartialModel n} :
    (M1.and M2).isSome ↔ M1.models ∩ M2.models ≠ ∅ := by
  simp only [and, VarSet.inter_eq_empty_iff, VarSet.mem_union, not_or, Option.pure_def,
    Option.isSome_dite]
  simp only [ne_eq, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and, not_forall, not_not]
  simp only [mem_models', exists_and_left, exists_prop]
  constructor
  · intro h1
    use fun i ↦ i ∈ M1.pos ∨ i ∈ M2.pos
    grind only
  · grind only

/-
lemma disjoint {n} {V : VarSet n} {M1 M2 : PartialModel V} {M} :
  M ∈ M1.models → M ∈ M2.models → M1 = M2 :=
  by
    simp only [models]
    intro hM1 hM2
    ext i hisorry
    specialize hM1 ⟨i, hi⟩
    specialize hM2 ⟨i, hi⟩
    simp_all
-/

end PartialModel

namespace Clause

def isTrivial_aux {n} (acc : Vector (Bool × Bool) n) : Clause n → Vector (Bool × Bool) n
  | [] => acc
  | ⟨i, true⟩ :: ls => isTrivial_aux (acc.set i (true, acc[i].2)) ls
  | ⟨i, false⟩ :: ls => isTrivial_aux (acc.set i (acc[i].1, true)) ls

lemma getElem_isTrivial_aux {n acc} {γ : Clause n} {b1 b2} {i} :
    (γ.isTrivial_aux acc)[i.val] = (b1, b2) ↔
    (b1 = acc[i].1 || ⟨i, true⟩ ∈ γ) ∧ (b2 = acc[i].2 || ⟨i, false⟩ ∈ γ) := by
  fun_induction isTrivial_aux
  case _ acc => grind only [← List.not_mem_nil, usr Fin.isLt, = Fin.getElem_fin]
  case _ acc j γ ih =>
    simp_all only [Fin.getElem_fin, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons,
      Bool.decide_or]
    constructor
    · grind only [= Vector.getElem_set]
    · intro h
      sorry
  sorry

def isTrivial {n} (γ : Clause n) : Bool :=
  (true, true) ∈ isTrivial_aux (Vector.replicate n (false, false)) γ

lemma isTrivial_iff' {n} {γ : Clause n} : isTrivial γ ↔ ∃ l ∈ γ, l.negate ∈ γ := by
  simp only [isTrivial, Vector.mem_iff_getElem', Fin.getElem_fin, getElem_isTrivial_aux,
    Vector.getElem_replicate, Bool.true_eq_false, decide_false, Bool.false_or, decide_eq_true_eq]
  constructor
  · grind [Literal.negate]
  · rintro ⟨⟨v, (true | false)⟩, h⟩
    all_goals grind [Literal.negate]

lemma isTrivial_iff {n} {γ : Clause n} : isTrivial γ ↔ γ.models = Set.univ := by
  sorry

lemma mem_models' {n} (γ : Clause n) (M : Model n) :
    M ∈ γ.models ↔ (∃ l ∈ γ, M ∈ l.models) ∨ γ.isTrivial := by
  simp_all only [mem_models, isTrivial_iff, Set.eq_univ_iff_forall, iff_self_or, implies_true]

end Formula.Clause

@[match_pattern]
def MODS.mk' {n} (vars : VarSet n) (mods : List (PartialModel n)) (prop : ∀ M ∈ mods, M.vars = vars)
    (reduced : ∀ i ∈ vars, ∃ M ∈ mods, ∀ M' ∈ mods,
      (∀ l : Literal n, l.var ≠ i → l ∈ M ↔ l ∈ M') → M = M') :
    MODS n := sorry

def RawMODS.reduce {n} : RawMODS n → MODS n := sorry

namespace MODS

def models {n} (φ : MODS n) : Models n :=
  { M | ∃ M' ∈ φ.inner.mods, M ∈ PartialModel.models M' }

@[simp]
lemma mem_models {n} {φ : MODS n} {M} : M ∈ φ.models ↔ ∃ M' ∈ φ.inner.mods, M ∈ M'.models := by
  simp [models]

@[no_expose]
public instance {n} : Formula n (MODS n) where

  vars φ := φ.inner.vars

  models := models

  models_equiv_right φ M M' := by
    simp only [mem_models, PartialModel.mem_models, Literal.mem_models]
    rintro h1 ⟨M'', h2, h3⟩
    use M'', h2
    have h4 := φ.inner.prop M'' h2
    simp only [← h4, PartialModel.mem_vars] at h1
    grind only

@[no_expose]
public instance {n} : Top n (MODS n) where

  top := ⟨⟨∅, [PartialModel.empty], by simp⟩, by simp⟩

  models_top := by
    simp only [Formula.models, Set.eq_univ_iff_forall, mem_models, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_left, PartialModel.models_empty, Set.mem_univ, implies_true]

@[no_expose]
public instance {n} : Bot n (MODS n) where

  bot := ⟨⟨∅, [], by simp⟩, by simp⟩

  vars_bot := by simp only [Formula.vars]

  models_bot := by
    simp only [Formula.models, Set.eq_empty_iff_forall_notMem, mem_models, List.not_mem_nil,
      false_and, exists_false, not_false_eq_true, implies_true]

@[no_expose]
public instance {n} : ClausalEntailment n (MODS n) where

  entails φ γ := φ.inner.mods.all (fun M ↦ γ.any fun l ↦ l ∈ M) || γ.isTrivial

  entails_iff := by
    intro φ γ
    simp only [Bool.or_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
      Formula.models, Set.subset_def, mem_models, forall_exists_index, and_imp]
    constructor
    · intro h M M' hM' hM
      rcases h with h | h
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hM'
        specialize h φ.inner.mods[i] hM'
        rcases h with ⟨l, h1, h2⟩
        rw [Clause.mem_models]
        use l, h1
        simp_all only [List.getElem_mem, PartialModel.mem_models]
      · rw [Clause.isTrivial_iff, Set.eq_univ_iff_forall] at h
        exact h M
    · simp only [Clause.mem_models', or_iff_not_imp_right]
      intro h1 h2 M hM
      by_contra h3
      obtain ⟨M', h4, h5⟩ : ∃ M', M' ∈ M.models ∧ M' ∉ γ.models := by
        let M' := fun i ↦ i ∈ M.pos ∨ ⟨i, false⟩ ∈ γ
        have hM' : M' ∈ M.models := by
          simp_all only [PartialModel.mem_models, Literal.mem_models, Bool.false_eq_true,
            not_false_eq_true, forall_const, PartialModel.mem_iff, Bool.not_eq_true, M']
          intro l hl
          rcases hl with ⟨h4, h5⟩ | ⟨h4, h5⟩
          · simp only [h4, true_or, h5]
          · simp only [h5, Bool.false_eq_true, iff_false, not_or]
            constructor
            · have := M.disjoint
              grind only [VarSet.inter_eq_empty_iff]
            · intro h6
              simp only [not_exists, not_and] at h3
              specialize h3 _ h6
              grind only [PartialModel.mem_iff]
        use M', hM'
        specialize h1 M' M hM hM' h2
        simp_all only [Clause.isTrivial_iff', not_exists, not_and, PartialModel.mem_models,
          Literal.mem_models, Clause.mem_models, not_true_eq_false, M']
        rcases h1 with ⟨l, h1, h4⟩
        rcases l with ⟨v, true | false⟩
        · grind only
        · simp_all
          specialize h3 _ h1
          specialize h2 _ h1
          grind only [Literal.negate, PartialModel.mem_iff]
      specialize h1 M' M hM h4 h2
      grind only [Clause.mem_models]

@[no_expose]
public instance {n} : Implicant n (MODS n) where

  entails δ φ :=
    -- restrict δ to φ.vars
    -- either extend δ to all PartialModels over φ.vars or reduce φ.vars and check whether it contains the partial model corresponding to δ
    sorry

  entails_iff := sorry

@[no_expose]
public instance {n} : BoundedConjuction n (MODS n) where

  and φ ψ := {
    vars := φ.vars ∪ ψ.vars
    mods := φ.mods.flatMap fun δ ↦ ψ.mods.filterMap fun δ' ↦ δ.and δ'
    prop := by
      simp only [List.mem_flatMap, List.mem_filterMap, forall_exists_index, and_imp]
      intro M M1 h1 M2 h2
      rw [← φ.prop M1 h1, ← ψ.prop M2 h2]
      exact PartialModel.vars_and
    reduced := sorry
    }

  models_and φ ψ := by
    simp only [Formula.models, Set.ext_iff, mem_models, List.mem_flatMap, List.mem_filterMap,
      Set.mem_inter_iff]
    intro M
    constructor
    · grind only [→ PartialModel.models_and, = Set.mem_inter_iff]
    · rintro ⟨⟨M1, hM1, h1⟩, M2, hM2, h2⟩
      have h3 : M1.models ∩ M2.models ≠ ∅ := by
        simp only [ne_eq, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_forall, not_not]
        use M
      rw [← PartialModel.isSome_and_iff, Option.isSome_iff_exists] at h3
      rcases h3 with ⟨M', hM'⟩
      grind only [= Set.mem_inter_iff, PartialModel.models_and hM']

@[no_expose]
public instance {n} : OfPartialModel n (MODS n) where

  ofPartialModel M := ⟨M.vars, [M], by simp, by simp⟩

  vars_ofPartialModel := by simp only [Formula.vars, implies_true]

  models_ofPartialModel := by simp only [Formula.models, models, List.mem_singleton, exists_eq_left,
    Set.ofPred_mem_eq, implies_true]

@[no_expose]
public instance {n} : Rename n (MODS n) where

  rename φ V r h1 := {
    vars :=  φ.vars.map r.rename
    mods := φ.mods.attach.map fun ⟨M, hM⟩ ↦ PartialModel.rename r M (φ.prop M hM ▸ h1)
    prop := by
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, forall_exists_index]
      intro M' M hM rfl
      simp only [← φ.prop M hM, SetLike.ext_iff, PartialModel.mem_vars_rename, VarSet.mem_map]
      grind only [PartialModel.mem_vars]
    reduced := by sorry
    }

  vars_rename φ V r h1 := by
    simp only [Formula.vars, VarSet.mem_map, Set.mem_image, SetLike.mem_coe]
    grind only

  models_rename φ V r h1 := by
    simp [Formula.models, Set.ext_iff]

@[no_expose]
public instance {n} : ToCNF n (MODS n) where

  toCNF := sorry

  models_toCNF := sorry

@[no_expose]
public instance {n} : ToDNF n (MODS n) where

  toDNF φ := φ.mods.map PartialModel.toCube

  models_toDNF := by
    simp only [Formula.models, Set.ext_iff, DNF.mem_models, List.mem_map, exists_exists_and_eq_and,
      PartialModel.models_toCube, mem_models, implies_true]

end Validator.MODS
