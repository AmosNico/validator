module

public import Validator.StateSetFormalism.Formula
import Std.Data.HashSet.Lemmas

-- TODO : make more efficient and move to Basic.lean

def Std.HashSet.filterMap {α} [BEq α] [Hashable α] {β} [BEq β] [Hashable β]
    (f : α → Option β) (m : Std.HashSet α) : Std.HashSet β :=
  Std.HashSet.ofList (m.toList.filterMap f)

@[simp]
lemma Std.HashSet.mem_filterMap {α} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {f : α → Option β} {m : Std.HashSet α} {b : β} :
    b ∈ m.filterMap f ↔ ∃ a ∈ m, f a = some b := by
  simp only [filterMap, mem_ofList, List.contains_eq_mem, List.mem_filterMap, mem_toList,
    decide_eq_true_eq]

def Std.HashSet.biUnion {α} [BEq α] [Hashable α] {β} [BEq β] [Hashable β]
    (f : α → Std.HashSet β) (m : Std.HashSet α) : Std.HashSet β :=
  Std.HashSet.ofList (m.toList.flatMap fun m ↦ (f m).toList)

@[simp]
lemma Std.HashSet.mem_flatMap {α} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {f : α → Std.HashSet β} {m : Std.HashSet α} {b : β} :
    b ∈ m.biUnion f ↔ ∃ a ∈ m, b ∈ f a := by
  simp only [biUnion, mem_ofList, List.contains_eq_mem, List.mem_flatMap, mem_toList,
    decide_eq_true_eq]

def Std.HashSet.attachMap {α} [BEq α] [LawfulBEq α] [Hashable α] {β} [BEq β] [Hashable β]
     (m : Std.HashSet α) (f : (a : α) → a ∈ m → β): Std.HashSet β :=
  Std.HashSet.ofList (m.toList.attach.map fun ⟨a, ha⟩ ↦ f a (Std.HashSet.mem_toList.1 ha))

@[simp]
lemma Std.HashSet.mem_attachMap {α} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {m : Std.HashSet α} {f : (a : α) → a ∈ m → β} {b : β} :
    b ∈ m.attachMap f ↔ ∃ a ha, f a ha = b := by
  simp only [attachMap, mem_ofList, List.contains_eq_mem, List.mem_map, List.mem_attach, true_and,
    Subtype.exists, mem_toList, decide_eq_true_eq]

namespace Validator
open Formula STRIPS

instance {n} : Hashable (PartialModel n) where
  hash M := mixHash (hash M.pos.toBitVec) (hash M.neg.toBitVec)

public structure RawMODS n where
  private vars : VarSet n
  private mods : Std.HashSet (PartialModel n)
  private vars_eq : ∀ M ∈ mods, M.vars = vars

public structure MODS n extends RawMODS n where
  /-- All variables in `vars` are needed for representing the formula. -/
  private reduced : ∀ i ∈ vars, ∃ M ∈ mods, ∀ M' ∈ mods,
    (∀ l : Literal n, l.var ≠ i → l ∈ M ↔ l ∈ M') → M = M'

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
    ext i hi
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

def RawMODS.reduce {n} : RawMODS n → MODS n :=
  sorry

def RawMODS.models {n} (φ : RawMODS n) : Models n :=
  { M | ∃ M' ∈ φ.mods, M ∈ M'.models }

@[simp]
lemma RawMODS.mem_models {n} {φ : RawMODS n} {M} : M ∈ φ.models ↔ ∃ M' ∈ φ.mods, M ∈ M'.models := by
  simp [models]

@[simp]
lemma RawMODS.models_reduce {n} {raw : RawMODS n} : raw.reduce.models = raw.models := sorry

namespace MODS

lemma mem_mods_iff_models{n} {φ : MODS n} {M} : M ∈ φ.mods ↔ M.models ⊆ φ.models := by
  constructor
  · grind only [= Set.subset_def, RawMODS.mem_models]
  · simp [Set.subset_def, RawMODS.mem_models]

    intro h
    have := φ.reduced
    sorry

@[no_expose]
public instance {n} : Formula n (MODS n) where

  vars φ := φ.vars

  models φ := φ.models

  models_equiv_right φ M M' := by
    simp only [RawMODS.mem_models, PartialModel.mem_models, Literal.mem_models]
    rintro h1 ⟨M'', h2, h3⟩
    use M'', h2
    have h4 := φ.vars_eq M'' h2
    simp only [← h4, PartialModel.mem_vars] at h1
    grind only

@[no_expose]
public instance {n} : Top n (MODS n) where

  top := ⟨⟨∅, {PartialModel.empty}, by simp⟩, by simp⟩

  models_top := by
    simp only [models, Std.HashSet.singleton_eq_insert, Set.eq_univ_iff_forall, RawMODS.mem_models,
      Std.HashSet.mem_insert, beq_iff_eq, Std.HashSet.not_mem_empty, or_false, exists_eq_left',
      PartialModel.models_empty, Set.mem_univ, implies_true]

@[no_expose]
public instance {n} : Bot n (MODS n) where

  bot := ⟨⟨∅, ∅, by simp⟩, by simp⟩

  vars_bot := by simp only [Formula.vars]

  models_bot := by
    simp only [Formula.models, Set.eq_empty_iff_forall_notMem, RawMODS.mem_models,
      Std.HashSet.not_mem_empty, false_and, exists_false, not_false_eq_true, implies_true]

@[no_expose]
public instance {n} : ClausalEntailment n (MODS n) where

  entails φ γ := φ.mods.all (fun M ↦ γ.any fun l ↦ l ∈ M) || γ.isTrivial

  entails_iff := by
    intro φ γ
    simp only [Bool.or_eq_true, Std.HashSet.all_eq_true_iff_forall_mem, List.any_eq_true,
      decide_eq_true_eq, models, Set.subset_def, RawMODS.mem_models, forall_exists_index, and_imp]
    constructor
    · intro h M M' hM' hM
      rcases h with h | h
      · specialize h M' hM'
        rcases h with ⟨l, h1, h2⟩
        rw [Clause.mem_models]
        use l, h1
        simp_all only [PartialModel.mem_models]
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
    match δ.toPartialModel with
    | some M => φ.vars ⊆ M.vars ∧ M ∈ φ.mods
    | none => true

  entails_iff δ φ := by
    cases heq : δ.toPartialModel with
    | none =>
      grind only [Cube.toPartialModel_eq_none_iff, Set.empty_subset]
    | some M =>
      simp only [decide_eq_true_eq, ← Cube.models_toPartialModel heq, Formula.models]
      sorry -- exact mem_mods_iff_models

@[no_expose]
public instance {n} : BoundedConjuction n (MODS n) where

  and φ ψ :=
    let raw : RawMODS n := {
      vars := φ.vars ∪ ψ.vars
      mods := φ.mods.biUnion fun δ ↦ ψ.mods.filterMap fun δ' ↦ δ.and δ'
      vars_eq := by
        simp only [Std.HashSet.mem_flatMap, Std.HashSet.mem_filterMap, forall_exists_index, and_imp]
        intro M M1 h1 M2 h2
        rw [← φ.vars_eq M1 h1, ← ψ.vars_eq M2 h2]
        exact PartialModel.vars_and
    }
    raw.reduce

  models_and φ ψ := by
    simp only [Formula.models, Set.ext_iff, RawMODS.mem_models, Std.HashSet.mem_flatMap,
      Std.HashSet.mem_filterMap, Set.mem_inter_iff, RawMODS.models_reduce]
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

  ofPartialModel M := ⟨⟨M.vars, {M}, by simp⟩, by simp⟩

  vars_ofPartialModel := by simp only [Formula.vars, implies_true]

  models_ofPartialModel := by simp only [models, RawMODS.models, Std.HashSet.singleton_eq_insert,
    Std.HashSet.mem_insert, beq_iff_eq, Std.HashSet.not_mem_empty, or_false, exists_eq_left',
    Set.ofPred_mem_eq, implies_true]

@[no_expose]
public instance {n} : Rename n (MODS n) where

  rename φ V r h1 := {
    vars :=  φ.vars.map r.rename
    mods :=
      φ.mods.attachMap fun M hM ↦ PartialModel.rename r M (φ.vars_eq M hM ▸ h1)
    vars_eq := by
      simp only [Std.HashSet.mem_attachMap, forall_exists_index]
      intro M' M hM rfl
      simp only [← φ.vars_eq M hM, SetLike.ext_iff, PartialModel.mem_vars_rename, VarSet.mem_map]
      grind only [PartialModel.mem_vars]
    reduced := sorry
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

  toDNF φ := φ.mods.toList.map PartialModel.toCube

  models_toDNF := by
    simp only [Formula.models, Set.ext_iff, DNF.mem_models, List.mem_map, Std.HashSet.mem_toList,
      exists_exists_and_eq_and, PartialModel.models_toCube, RawMODS.mem_models, implies_true]

end Validator.MODS
