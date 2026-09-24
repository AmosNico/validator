module

public import Validator.StateSetFormalism.Formula

namespace Validator
open Formula STRIPS

public structure MODS n where
  private vars : VarSet n
  private mods : List (PartialModel n)
  private prop : ∀ M ∈ mods, M.vars = vars
  deriving DecidableEq

namespace Clause

def isTrivial_aux {n} (acc : Vector (Bool × Bool) n) : Clause n → Vector (Bool × Bool) n
  | [] => acc
  | ⟨i, true⟩ :: ls => isTrivial_aux (acc.set i (true, acc[i].2)) ls
  | ⟨i, false⟩ :: ls => isTrivial_aux (acc.set i (acc[i].1, true)) ls

lemma getElem_isTrivial_aux {n acc} {γ : Clause n} {i} :
    (γ.isTrivial_aux acc)[i.val] = (acc[i].1 || ⟨i, true⟩ ∈ γ, acc[i].2 || ⟨i, false⟩ ∈ γ) := by
  fun_induction isTrivial_aux
  case _ acc => grind only [← List.not_mem_nil, usr Fin.isLt, = Fin.getElem_fin]
  case _ acc j γ ih =>
    simp only [List.mem_cons, Literal.mk.injEq, and_true, Bool.decide_or,
      Bool.false_eq_true, and_false, false_or]
    rw [ih, Prod.mk_inj]
    grind
  case _ acc j γ ih =>
    simp only [List.mem_cons, Literal.mk.injEq, Bool.true_eq_false, and_false,
      false_or, and_true, Bool.decide_or]
    rw [ih, Prod.mk_inj]
    grind

def isTrivial {n} (γ : Clause n) : Bool :=
  (true, true) ∈ isTrivial_aux (Vector.replicate n (false, false)) γ

lemma isTrivial_iff' {n} {γ : Clause n} : isTrivial γ ↔ ∃ l ∈ γ, l.negate ∈ γ := by
  simp only [isTrivial, Vector.mem_iff_getElem', Fin.getElem_fin, getElem_isTrivial_aux,
    Vector.getElem_replicate, Bool.false_or, decide_eq_true_eq]
  simp only [Literal.exists_iff, Bool.exists_bool]
  grind only [Literal.negate_eq]

lemma isTrivial_iff {n} {γ : Clause n} : isTrivial γ ↔ γ.models = Set.univ := by
  rw [isTrivial_iff']
  constructor
  · rintro ⟨l, h1, h2⟩
    ext M
    simp only [mem_models, Set.mem_univ, iff_true]
    grind only [!Literal.models_negate, = Set.mem_compl_iff]
  · intro h1
    simp only [Set.ext_iff, mem_models, Set.mem_univ, iff_true] at h1
    obtain ⟨l, hl, h2⟩ := h1 fun i ↦ ⟨i, false⟩ ∈ γ
    use l, hl
    rcases l with ⟨i, (_ | _)⟩
    · grind only [Literal.mem_models]
    · grind only [Literal.mem_models, Literal.negate_eq]

lemma mem_models' {n} (γ : Clause n) (M : Model n) :
    M ∈ γ.models ↔ (∃ l ∈ γ, M ∈ l.models) ∨ γ.isTrivial := by
  simp_all only [mem_models, isTrivial_iff, Set.eq_univ_iff_forall, iff_self_or, implies_true]

end Clause
namespace MODS

def models {n} (φ : MODS n) : Models n :=
  { M | ∃ M' ∈ φ.mods, M ∈ PartialModel.models M' }

@[simp]
lemma mem_models {n} {φ : MODS n} {M} : M ∈ φ.models ↔ ∃ M' ∈ φ.mods, M ∈ M'.models := by
  simp [models]

lemma restrict_mem_mods {n} {φ : MODS n} {M : PartialModel n} (h : φ.vars ⊆ M.vars) :
    M.restrict φ.vars ∈ φ.mods ↔ M.models ⊆ φ.models := by
  simp only [Set.subset_def, mem_models]
  constructor
  · grind only [PartialModel.mem_models', !PartialModel.pos_restrict, !PartialModel.neg_restrict,
      VarSet.mem_inter]
  · intro h'
    have h1 : ∀ i ∈ M.neg, i ∉ M.pos := by
      grind only [VarSet.inter_eq_empty_iff, M.disjoint]
    specialize h' (fun i ↦ i ∈ M.pos) (by grind only [PartialModel.mem_models'])
    rcases h' with ⟨M', h2, h3⟩
    have h4 : M.restrict φ.vars = M' := by
      simp [PartialModel.mem_models'] at h3
      rw [← φ.prop M' h2] at ⊢ h
      ext i
      · grind only [PartialModel.vars_eq, !PartialModel.pos_restrict, VarSet.mem_inter,
          VarSet.mem_union]
      · have : ∀ i ∈ M'.neg, i ∈ M.neg := by
          simp only [PartialModel.vars_eq, VarSet.subset_iff, VarSet.mem_union] at h
          grind only
        grind only [PartialModel.vars_eq, !PartialModel.neg_restrict, VarSet.mem_inter,
          VarSet.mem_union]
    simp only [h4, h2]

lemma models_subset_models_iff {n} {φ : MODS n} {M : PartialModel n} :
    M.models ⊆ φ.models ↔ ∀ M' ∈ (M.restrict φ.vars).expand φ.vars, M' ∈ φ.mods := by
  simp only [PartialModel.expand_restrict, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h1 M' hM'
    have h2 := PartialModel.subset_models_of_expand M' hM'
    have h3 := Set.Subset.trans h2 h1
    have h4 : φ.vars ⊆ M'.vars := by
      rw [PartialModel.vars_of_mem_expand hM']
      simp only [VarSet.subset_iff, VarSet.mem_union]
      tauto
    rwa [← restrict_mem_mods h4] at h3
  · intro h1 M' hM'
    rw [M.models_expand φ.vars] at hM'
    simp only [Set.mem_iUnion, exists_prop] at hM'
    rcases hM' with ⟨M'', h2, hM'⟩
    specialize h1 M'' h2
    rw [PartialModel.mem_expand] at h2
    simp only [mem_models]
    grind only [PartialModel.mem_models', !PartialModel.pos_restrict, !PartialModel.neg_restrict,
      VarSet.mem_inter]

@[no_expose]
public instance {n} : Formula n (MODS n) where

  vars φ := φ.vars

  models := models

  models_equiv_right φ M M' := by
    simp only [mem_models, PartialModel.mem_models, Literal.mem_models]
    rintro h1 ⟨M'', h2, h3⟩
    use M'', h2
    have h4 := φ.prop M'' h2
    simp only [← h4, PartialModel.mem_vars] at h1
    grind only

@[no_expose]
public instance {n} : Top n (MODS n) where

  top := ⟨∅, [PartialModel.empty], by simp⟩

  models_top := by
    simp only [Formula.models, Set.eq_univ_iff_forall, mem_models, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_left, PartialModel.models_empty, Set.mem_univ, implies_true]

@[no_expose]
public instance {n} : Bot n (MODS n) where

  bot := ⟨∅, [], by simp⟩

  vars_bot := by simp only [Formula.vars]

  models_bot := by
    simp only [Formula.models, Set.eq_empty_iff_forall_notMem, mem_models, List.not_mem_nil,
      false_and, exists_false, not_false_eq_true, implies_true]

@[no_expose]
public instance {n} : ClausalEntailment n (MODS n) where

  entails φ γ := φ.mods.all (fun M ↦ γ.any fun l ↦ l ∈ M) || γ.isTrivial

  entails_iff := by
    intro φ γ
    simp only [Bool.or_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
      Formula.models, Set.subset_def, mem_models, forall_exists_index, and_imp]
    constructor
    · intro h M M' hM' hM
      rcases h with h | h
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hM'
        specialize h φ.mods[i] hM'
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
          grind only [Literal.negate_eq, PartialModel.mem_iff]
      specialize h1 M' M hM h4 h2
      grind only [Clause.mem_models]

@[no_expose]
public instance {n} : Implicant n (MODS n) where

  entails δ φ := match δ.toPartialModel with
    | some M =>
      if φ.vars ⊆ M.vars then
        M.restrict φ.vars ∈ φ.mods
      else
        M.restrict φ.vars |>.expand φ.vars |>.all (· ∈ φ.mods)
    | none => true

  entails_iff δ φ := by
    simp only [Formula.models]
    split
    next M h1 =>
      rw [← Cube.models_toPartialModel h1]
      split
      next h2 => simp only [restrict_mem_mods h2, decide_eq_true_eq]
      next h2 => simp only [List.all_eq_true, decide_eq_true_eq, models_subset_models_iff]
    next h =>
      rw [Cube.toPartialModel_eq_none_iff] at h
      simp only [h, Set.empty_subset]

@[no_expose]
public instance {n} : BoundedConjuction n (MODS n) where

  and φ ψ := {
    vars := φ.vars ∪ ψ.vars
    mods := φ.mods.flatMap fun δ ↦ ψ.mods.filterMap fun δ' ↦ δ.and? δ'
    prop := by
      simp only [List.mem_flatMap, List.mem_filterMap, forall_exists_index, and_imp]
      intro M M1 h1 M2 h2
      rw [← φ.prop M1 h1, ← ψ.prop M2 h2]
      grind only [= PartialModel.and?_eq_some_iff, = PartialModel.vars_and]
    }

  models_and φ ψ := by
    simp only [Formula.models, Set.ext_iff, mem_models, List.mem_flatMap, List.mem_filterMap,
      Set.mem_inter_iff]
    intro M
    constructor
    · grind only [= PartialModel.and?_eq_some_iff, → PartialModel.models_and, = Set.mem_inter_iff]
    · rintro ⟨⟨M1, hM1, h1⟩, M2, hM2, h2⟩
      have h3 : M1.Compatible M2 := by
        simp only [PartialModel.compatible_iff_models, Set.nonempty_def, Set.mem_inter_iff]
        use M
      use M1.and M2 h3
      grind only [= PartialModel.models_and, = Set.mem_inter_iff, = PartialModel.and?_eq_some_iff]

@[no_expose]
public instance {n} : SententialEntailment n (MODS n) where

  entails φ ψ := sorry

  entails_iff := sorry

@[no_expose]
public instance {n} : OfPartialModel n (MODS n) where

  ofPartialModel M := ⟨M.vars, [M], by simp⟩

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
