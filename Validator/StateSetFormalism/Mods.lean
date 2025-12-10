import Validator.StateSetFormalism.Formula

namespace Validator

open Formula

-- TODO : clean up

structure MODS n where
  vars : VarSet' n
  mods : List (PartialModel vars)
  deriving DecidableEq, Repr
  -- No duplicates?

namespace Formula.PartialModel
/-
def toStates {n} {V : VarSet' (2 * n)} (M : PartialModel V) : States n :=
  M.models.image Model.unprimedState

lemma mem_toStates {n} {V : VarSet' (2 * n)} {M : PartialModel V} {s : State n} :
  s ∈ M.toStates ↔ ∀ i : Fin V.val.length, Even V.val[i] → (M[i] ↔ ⟨V.val[i] / 2, by omega⟩ ∈ s) :=
  by
    simp [toStates, Model.unprimedState, Fin.toUnprimed]
    constructor
    · rintro ⟨M', hM', rfl⟩ i h2
      simp [PartialModel.models] at hM'
      specialize hM' i
      simp_all [Fin.even_iff_of_even, Nat.two_mul_div_two_of_even]
    · intro h1
      let M' : Model (2 * n) := fun ⟨i, hi⟩ ↦
        match V.val.finIdxOf? ⟨i,hi⟩ with
          | none => ⟨i / 2, by omega⟩ ∈ s
          | some j => M[j]
      have hM' : M' ∈ M.models := by
        simp [M', models]
        rintro ⟨j, hj⟩
        specialize h1 ⟨j, hj⟩
        split
        case h_1 h =>
          grind
        case h_2 _ j' h2  =>
          rcases j' with ⟨j', hj'⟩
          obtain ⟨rfl⟩ : j = j' := by
            have h3 := List.Sorted.nodup V.prop
            rw [← List.Nodup.getElem_inj_iff h3 (hi := hj) (hj := hj')]
            simp at h2 ⊢
            simp_all only
          rfl
      use M', hM'
      ext i
      simp [M']
      split
      case h_1 => simp
      case h_2 _ j h2 =>
        simp at h2
        have h3 : Even V.val[j] := by
          simp [Fin.even_iff_of_even, h2.1]
        specialize h1 j h3
        simp_all
-/
lemma models_nonempty {n} {V : VarSet' n} (M : PartialModel V) : Nonempty M.models :=
  by
    constructor
    use fun i ↦ (List.finRange V.val.length).any fun j ↦ V.val[j].val = i && M[j]
    simp [models]
    rintro ⟨i, hi⟩
    rcases V with ⟨l, h⟩
    simp [← Fin.ext_iff]
    rw [← Bool.coe_iff_coe]
    have : ∀ i {_ : i < l.length} j {_ : j < l.length}, l[i] = l[j] ↔ i = j := by
      simp [List.Sorted, List.pairwise_iff_getElem] at h
      grind only
    simp
    grind

lemma disjoint {n} {V : VarSet' n} {M1 M2 : PartialModel V} {M} :
  M ∈ M1.models → M ∈ M2.models → M1 = M2 :=
  by
    simp [models]
    intro hM1 hM2
    ext i hi
    specialize hM1 ⟨i, hi⟩
    specialize hM2 ⟨i, hi⟩
    simp_all

-- TODO : Make more efficient
def contains_literal {n} {V : VarSet' n} (M : PartialModel V) : Literal n → Bool
| ⟨var, b⟩ => (List.finRange V.val.length).any (fun i ↦ V.val[i] = var && M[i] = b)

-- TODO : remove?
lemma contains_literal_iff {n} {V : VarSet' n} (M : PartialModel V) (l : Literal n) :
  M.contains_literal l ↔ ∃ i : Fin V.val.length, V.val[i] = l.1 ∧ M[i] = l.2 :=
  by simp [contains_literal]

lemma mem_models_to_mem_literal_models
  {n} {V : VarSet' n} {M : PartialModel V} {l : Literal n} {M'} :
  M.contains_literal l → M' ∈ M.models →  M' ∈ l.models :=
  by
    simp [models, Literal.mem_models, contains_literal]
    intro i h1 h2 h3
    rw [← h1, ← h2]
    exact h3 i

end Formula.PartialModel

namespace MODS

/-
def toStates {n} (φ : MODS n) : States n :=
  φ.models.toList.biUnion Model.toStates

@[simp]
lemma mem_toStates {n} {φ : MODS n} {s} : s ∈ φ.toStates ↔ ∃ M ∈ φ.models, s ∈ M.toStates :=
  by
    simp [toStates]

#eval [∅, {0}, {1}, {0,1}].map
  (fun x ↦ decide (x ∈ MODS.toStates ⟨(⟨#[0], by simp⟩ : OrderedVars (2 + 2)), #[#v[true]]⟩))
-/

def models {n} (φ : MODS n) : Models n :=
  { M | ∃ M' ∈ φ.mods, M ∈ PartialModel.models M' }

@[simp]
lemma mem_models {n} {φ : MODS n} {M} : M ∈ φ.models ↔ ∃ M' ∈ φ.mods, M ∈ M'.models :=
  by
    simp [models]

instance {n} : Formula n (MODS n) where

  vars φ := φ.vars

  models := models

  models_equiv_right := sorry

/-
  ofModel {V} M := MODS.mk V #[M]

  ofModel_correct :=
    by
      intro V M
      ext s
      simp
-/

instance {n} : Top n (MODS n) where

  top := sorry

  top_correct := sorry

instance {n} : Bot n (MODS n) where

  bot := sorry

  bot_correct := sorry

/- TODO : remove
instance {n} : ModelTesting n (MODS n) where

  isModel φ M := φ.mods.contains M

  isModel_correct :=
    by
      intro φ mod
      simp [Formula.models]
      constructor
      · tauto
      · intro h1
        obtain ⟨M, h2⟩ := mod.models_nonempty
        obtain ⟨M', hM', h3⟩ := h1 h2
        rw [PartialModel.disjoint h2 h3]
        exact hM'
-/

instance {n} : ClausalEntailment n (MODS n) where

  -- This only seems to work is all variables of γ are in φ.vars
  -- Otherwise, if p ∉ φ.vars, then γ := p ∨ ¬ p causes problems
  entails φ γ := φ.mods.all (fun M ↦ γ.any M.contains_literal) || γ.isTrivial

  entails_correct :=
    by
      intro φ γ
      sorry
      /-
      simp [Formalism.models, Finset.subset_iff, Clause.isTrivial_iff, -Bool.exists_bool, -Bool.forall_bool]
      constructor
      · rintro h s M hM hs
        obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hM
        rcases h with h | ⟨x, h⟩
        · specialize h i hi
          rcases h with ⟨var, b, h1, h2⟩
          use var, b, h1
          exact Model.mem_model_to_mem_literal h2 hs
        · if h : x ∈ s then
            use x, true
            simp_all [Literal.mem_toFinset]
            sorry
          else
            use x, false
            simp_all [Literal.mem_toFinset]
            sorry
      · intro h
        if h' : ∃ x, (x, true) ∈ γ ∧ (x, false) ∈ γ then
          exact Or.inr h'
        else
          apply Or.inl
          intro i hi
          obtain ⟨s, hs⟩ := Model.nonempty φ.models[i]
          rcases h φ.models[i] (by simp) hs with ⟨var, b, h1, h2⟩
          use var, b, h1
          simp [Model.mem_iff] at hs
          simp_all [Literal.mem_toFinset, Model.contains_literal_iff]

          by_contra h3
          simp at h3
          obtain ⟨j, hj, h3⟩ := List.getElem_of_mem h1

          sorry-/


instance {n} : BoundedConjuction n (MODS n) where

  and φ ψ := sorry

  and_correct := sorry

instance {n} : SententialEntailment n (MODS n) where

  entails φ ψ := sorry

  entails_correct := sorry

instance {n} : OfPartialModel n (MODS n) where

  ofPartialModel := sorry

  ofPartialModel_correct := sorry

instance {n} : Renaming n (MODS n) where

  rename := sorry

  rename_correct := sorry

instance {n} : ToCNF n (MODS n) where

  toCNF := sorry

  toCNF_correct := sorry

/-
def models {n} (pt : STRIPS n) (φ : ConstantStateSet) : Models (2 * n) :=
  (φ.partialModel pt).snd.models
-/
/-
  constant
  | .empty => ⟨mkEmpty n, VarSet'.isUnprimed_unprimedVars⟩
  | .init => ⟨mkInit pt, VarSet'.isUnprimed_unprimedVars⟩
  | .goal => ⟨mkGoal pt, by
    simp [mkGoal, Formula.vars]
    exact VarSet'.isUnprimed_toUnprimed⟩

/-
  constant_eq
  | .empty => by
    simp [mkEmpty, Formula.models, models, List.biUnion]
  | .init => by
    ext s
    simp [mkInit, Formula.models]
    constructor
    · rintro ⟨M, ⟨M', h1, h2⟩, rfl⟩
      simp_all [unprimedVars]
      rw [Vector.toArray_inj] at h1
      sorry
    · obtain ⟨M, hM⟩ := Model.exists_model_of_state s
      sorry
    rw [Vector.toArray_inj]

    sorry
  | .goal => sorry
-/
  constant_eq
  | .empty => by
    simp [mkEmpty, ConstantStateSet.toStates]
  | .init => by
    ext s
    simp [mkInit, PartialModel.mem_toStates, VarSet'.unprimedVars, Fin.toUnprimed]
    constructor
    · rintro h ⟨i, hi⟩
      specialize h ⟨i, by simp [hi]⟩ (by simp [Fin.even_iff_of_even])
      simp_all
    · intro h
      rintro ⟨i, hi⟩
      simp [h ⟨i, by simp_all only [List.length_ofFn]⟩]
  | .goal => by
    ext s
    simp [mkGoal, PartialModel.mem_toStates, VarSet'.toUnprimed, Fin.toUnprimed]
    constructor
    · rintro h i hi
      obtain ⟨j, hj, h1⟩ := List.getElem_of_mem hi
      specialize h ⟨j, by simp [hj]⟩ (by simp [Fin.even_iff_of_even])
      simp_all
    · intro h
      rintro ⟨i, hi⟩ h1
      apply h
      simp
-/
end MODS

/-
namespace old

abbrev Model k := BitVec k

structure Mods n where
  vars : VarSet' n
  models : Array (Model vars.size)
  -- No duplicates?

def Mods.toFinset {n} (φ : Mods n) : States n :=
  Array.foldl (fun S M ↦ S ∪ Model.toFinset M) ∅ φ.models where

  toModel (s : State n) : Model φ.vars.size :=
    BitVec.ofFnLE (fun i ↦ decide (φ.vars[i] ∈ s))

  Model.toFinset : Model φ.vars.size → States n
  | M => {s ∈ (Fintype.elems : States n) | toModel s = M}

#eval [∅, {0}, {1}, {0,1}].map (fun x ↦ decide (x ∈ Mods.toFinset ⟨(#[1] : VarSet' 2), #[]⟩))

instance {n} : Formalism n (Mods n) where

  OrderedVars φ := φ.vars

  toFinset := Mods.toFinset

instance {n} : BoundedConjuction n (Mods n) where

  and φ ψ := sorry

  and_correct := sorry

instance {n} : SententialEntailment' n (Mods n) where

  entails φ ψ h := sorry

  entails_correct := sorry

end old
-/
/-
CE -> is_entailed
bool ModsStateSet::is_entailed(const VariableOrder &OrderedVars,
                               const std::vector<bool> &clause) const {
    std::vector<std::pair<int,int>> possible_checks;
    for (size_t i = 0; i < OrderedVars.size(); ++i) {
        for (size_t j = 0; j < formula.get_variable_order().size(); ++j) {
            if (OrderedVars[i] == formula.get_variable_order()[j]) {
                possible_checks.push_back({i,j});
                break;
            }
        }
    }
    auto it = formula.get_cbegin();
    while (it != formula.get_cend()) {
        const Model &model = *it;
        bool covered = false;
        for (std::pair<int,int> check : possible_checks) {
            if (model[check.second] == clause[check.first]) {
                covered = true;
                break;
            }
        }
        if (!covered) {
            return false;
        }
        it++;
    }
    return true;
}
-/

end Validator
