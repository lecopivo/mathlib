/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import data.sum
import tactic.core
import data.buffer.parser

universes u v w

open native tactic.interactive


namespace list

variables {α : Type u} {β : Type v}

def mfirst' {m : Type v → Type w} [monad m] (f : α → m (option β)) :
  list α → m (option β)
| [] := pure none
| (a :: as) := do
  (some b) ← f a | mfirst' as,
  pure (some b)

def to_rbmap : list α → rbmap ℕ α :=
foldl_with_index (λ i mapp a, mapp.insert i a) (mk_rbmap ℕ α)

meta def to_rb_map {α : Type} : list α → rb_map ℕ α :=
foldl_with_index (λ i mapp a, mapp.insert i a) mk_rb_map

def all_some : list (option α) → option (list α)
| [] := some []
| (some x :: xs) := (::) x <$> all_some xs
| (none :: xs) := none

def take_lst {α} : list α → list ℕ → list (list α) × list α
| xs [] := ([], xs)
| xs (n :: ns) :=
  let ⟨xs₁, xs₂⟩ := xs.split_at n in
  let ⟨xss, rest⟩ := take_lst xs₂ ns in
  (xs₁ :: xss, rest)

def map₂_left' {α β γ} (f : α → option β → γ) : list α → list β → (list γ × list β)
| [] bs := ([], bs)
| (a :: as) [] :=
  let ⟨cs, rest⟩ := map₂_left' as [] in
  (f a none :: cs, rest)
| (a :: as) (b :: bs) :=
  let ⟨cs, rest⟩ := map₂_left' as bs in
  (f a (some b) :: cs, rest)

def map₂_right' {α β γ} (f : option α → β → γ) (as : list α) (bs : list β) :
  (list γ × list α) :=
map₂_left' (flip f) bs as

def zip_left' {α β} : list α → list β → list (α × option β) × list β :=
map₂_left' (λ a b, (a, b))

def zip_right' {α β} : list α → list β → list (option α × β) × list α :=
map₂_right' (λ a b, (a, b))

def map₂_left {α β γ} (f : α → option β → γ) : list α → list β → list γ
| [] _ := []
| (a :: as) [] := f a none :: map₂_left as []
| (a :: as) (b :: bs) := f a (some b) :: map₂_left as bs

def map₂_right {α β γ} (f : option α → β → γ) (as : list α) (bs : list β) :
  list γ :=
map₂_left (flip f) bs as

def zip_left {α β} : list α → list β → list (α × option β) :=
map₂_left prod.mk

def zip_right {α β} : list α → list β → list (option α × β) :=
map₂_right prod.mk

lemma map₂_left_eq_map₂_left' {α β γ} (f : α → option β → γ)
  : ∀ (as : list α) (bs : list β),
    map₂_left f as bs = (map₂_left' f as bs).fst
| [] bs := by simp!
| (a :: as) [] := by { simp! only [*], cases (map₂_left' f as nil), simp!  }
| (a :: as) (b :: bs) := by { simp! only [*], cases (map₂_left' f as bs), simp! }

def fill_nones {α} : list (option α) → list α → list α
| [] _ := []
| ((some a) :: as) as' := a :: fill_nones as as'
| (none :: as) [] := as.reduce_option
| (none :: as) (a :: as') := a :: fill_nones as as'

end list


namespace expr

meta def locals (e : expr) : expr_set :=
e.fold mk_expr_set $ λ e _ occs,
  if e.is_local_constant then occs.insert e else occs

meta def local_unique_names (e : expr) : name_set :=
e.fold mk_name_set $ λ e _ occs,
  match e with
  | (local_const u _ _ _) := occs.insert u
  | _ := occs
  end

end expr


namespace name

open parser

/--
After elaboration, Lean does not have non-dependent function types with
unnamed arguments. This means that for the declaration

```lean
inductive test : Type :=
| intro : unit → test
```

the type of `test.intro` becomes

```lean
test.intro : ∀ (a : unit), test
```lean

after elaboration, where `a` is an auto-generated name.

This means that we can't know for sure whether a constructor argument was named
by the user. Hence the following hack: If an argument is non-dependent *and* its
name is `a` or `a_n` for some `n ∈ ℕ`, then we assume that this name was
auto-generated rather than chosen by the user.
-/
library_note "unnamed constructor arguments"

/-- See [note unnamed constructor arguments]. -/
meta def likely_generated_name_p : parser unit := do
  ch 'a',
  optional (ch '_' *> nat),
  pure ()

/-- See [note unnamed constructor arguments]. -/
meta def is_likely_generated_name (n : name) : bool :=
match n with
| anonymous := ff
| mk_numeral _ _ := ff
| mk_string s anonymous := (likely_generated_name_p.run_string s).is_right
| mk_string _ _ := ff
end

end name


namespace tactic

open expr

meta def open_pis_whnf_dep :
  expr → tactic (list (expr × bool) × expr) := λ e, do
  e' ← whnf e,
  match e' with
  | (pi n bi t rest) := do
    c ← mk_local' n bi t,
    let dep := rest.has_var,
    (cs, rest) ← open_pis_whnf_dep $ rest.instantiate_var c,
    pure ((c, dep) :: cs, rest)
  | _ := pure ([], e)
  end

meta def open_n_pis_metas' :
  expr → ℕ → tactic (list (expr × name × binder_info) × expr)
| e 0 := pure ([], e)
| (pi nam bi t rest) (n + 1) := do
  m ← mk_meta_var t,
  (ms, rest) ← open_n_pis_metas' (rest.instantiate_var m) n,
  pure ((m, nam, bi) :: ms, rest)
| e (n + 1) := fail! "expected an expression starting with a Π, but got: {e}"

/--
Update the type of a local constant or metavariable. For local constants and
metavariables obtained via, for example, `tactic.get_local`, the type stored in
the expression is not necessarily the same as the type returned by `infer_type`.
This tactic, given a local constant or metavariable, updates the stored type to
match the output of `infer_type`. If the input is not a local constant or
metavariable, `update_type` does nothing.
-/
meta def update_type : expr → tactic expr
| e@(local_const ppname uname binfo _) :=
  local_const ppname uname binfo <$> infer_type e
| e@(mvar ppname uname _) :=
  mvar ppname uname <$> infer_type e
| e := pure e

/--
Given a hypothesis (local constant) `h` and a local constant `i`, we say that
`h` depends on `i` iff

- `i` appears in the type of `h` or
- `h` is a local definition and `i` appears in its body.

We say that `h` inclusively depends on `i` iff `h` depends on `i` or `h = i`
(so inclusive dependency is the reflexive closure of regular dependency).

For example, consider the following context:

```lean
P : ∀ n, fin n → Prop
n : ℕ
m : ℕ := n
f : fin m
h : P m f
```

Here, `m` depends on `n`; `f` depends on `m`; `h` depends on `P`, `m` and `f`.
Note that `f` and `h` do not depend on `n`, so the depends-on relation is not
transitive. `h` inclusively depends on `h`, `P`, `m` and `f`.

We also say that `m` is a dependency of `f` and `f` a reverse dependency of `m`.
Note that the Lean standard library sometimes uses these terms differently:
`kdependencies`, confusingly, computes the reverse dependencies of an
expression.
-/
library_note "dependencies of hypotheses"


/--
`type_has_local_in h ns` returns true iff the type of `h` contains a local
constant whose unique name appears in `ns`.
-/
meta def type_has_local_in (h : expr) (ns : name_set) : tactic bool := do
  h_type ← infer_type h,
  pure $ h_type.has_local_in ns

/--
`local_def_value_has_local_in h ns` returns true iff `h` is a local definition
whose body contains a local constant whose unique name appears in `ns`.
-/
meta def local_def_value_has_local_in (h : expr) (ns : name_set) : tactic bool := do
  (some h_val) ← try_core $ local_def_value h | pure ff,
  pure $ h_val.has_local_in ns

/--
Given a hypothesis `h`, `hyp_depends_on_locals h ns` returns true iff `h`
depends on a local constant whose unique name appears in `ns`. See note
[dependencies of hypotheses].
-/
meta def hyp_depends_on_locals (h : expr) (ns : name_set) : tactic bool :=
list.mbor
  [ type_has_local_in h ns,
    local_def_value_has_local_in h ns ]

/--
Given a hypothesis `h`, `hyp_depends_on_locals h ns` returns true iff `h`
inclusively depends on a local constant whose unique name appears in `ns`.
See note [dependencies of hypotheses].
-/
meta def hyp_depends_on_locals_inclusive (h : expr) (ns : name_set) : tactic bool :=
list.mbor
  [ pure $ ns.contains h.local_uniq_name,
    hyp_depends_on_locals h ns ]

/--
Given a hypothesis `h` and local constant `i`, `hyp_depends_on_local h i`
checks whether `h` depends on `i`. See note [dependencies of hypotheses].
-/
meta def hyp_depends_on_local (h i : expr) : tactic bool :=
hyp_depends_on_locals h (mk_name_set.insert i.local_uniq_name)

/--
Given a hypothesis `h` and local constant `i`, `hyp_depends_on_local h i`
checks whether `h` inclusively depends on `i`. See note
[dependencies of hypotheses].
-/
meta def hyp_depends_on_local_inclusive (h i : expr) : tactic bool :=
hyp_depends_on_locals_inclusive h (mk_name_set.insert i.local_uniq_name)

/--
Given a hypothesis `h`, `dependencies_of_hyp' h` returns the set of unique names
of the local constants which `h` depends on. See note
[dependencies of hypotheses].
-/
meta def dependencies_of_hyp' (h : expr) : tactic name_set := do
  t ← infer_type h,
  let deps := t.local_unique_names,
  (some val) ← try_core $ local_def_value h | pure deps,
  let deps := deps.union val.local_unique_names,
  pure deps

/--
Given a hypothesis `h`, `dependencies_of_hyp h` returns the hypotheses which `h`
depends on. See note [dependencies of hypotheses].
-/
meta def dependencies_of_hyp (h : expr) : tactic (list expr) := do
  ns ← dependencies_of_hyp' h,
  ns.to_list.mmap get_local

/--
Given a hypothesis `h`, `dependencies_of_hyp_inclusive' h` returns the set of
unique names of the local constants which `h` inclusively depends on. See note
[dependencies of hypotheses].
-/
meta def dependencies_of_hyp_inclusive' (h : expr) : tactic name_set := do
  deps ← dependencies_of_hyp' h,
  pure $ deps.insert h.local_uniq_name

/--
Given a hypothesis `h`, `dependencies_of_hyp_inclusive' h` returns the
hypotheses which `h` inclusively depends on. See note
[dependencies of hypotheses].
-/
meta def dependencies_of_hyp_inclusive (h : expr) : tactic (list expr) := do
  ns ← dependencies_of_hyp_inclusive' h,
  ns.to_list.mmap get_local

/--
Given a set `ns` of unique names of hypotheses,
`reverse_dependencies_of_hyps' hs` returns those hypotheses which depend on any
of the `hs`, excluding the `hs` themselves. See note
[dependencies of hypotheses].
-/
meta def reverse_dependencies_of_hyps' (hs : name_set) : tactic (list expr) := do
  ctx ← local_context,
  ctx.mfilter $ λ h, list.mband
    [ pure $ ¬ hs.contains h.local_uniq_name,
      hyp_depends_on_locals h hs ]

/--
`reverse_dependencies_of_hyps hs` returns those hypotheses which depend on any
of the hypotheses `hs`, excluding the `hs` themselves.
-/
meta def reverse_dependencies_of_hyps (hs : list expr) : tactic (list expr) :=
reverse_dependencies_of_hyps' $
  hs.foldl (λ ns h, ns.insert h.local_uniq_name) mk_name_set

/--
Given a set `ns` of unique names of hypotheses,
`reverse_dependencies_of_hyps_inclusive' hs` returns those hypotheses which
inclusively depend on any of the `hs`. See note [dependencies of hypotheses].

This is the 'revert closure' of `hs`: to revert the `hs`, we must also revert
their reverse dependencies.
-/
meta def reverse_dependencies_of_hyps_inclusive' (hs : name_set) :
  tactic (list expr) := do
  ctx ← local_context,
  ctx.mfilter $ λ h, hyp_depends_on_locals_inclusive h hs

/--
`reverse_dependencies_of_hyps_inclusive hs` returns those hypotheses which
inclusively depend on any of the hypotheses `hs`. See note
[dependencies of hypotheses].

This is the 'revert closure' of `hs`: to revert the `hs`, we must also revert
their reverse dependencies.
-/
meta def reverse_dependencies_of_hyps_inclusive (hs : list expr) :
  tactic (list expr) := do
reverse_dependencies_of_hyps_inclusive' $
  hs.foldl (λ ns h, ns.insert h.local_uniq_name) mk_name_set

/--
Revert the local constants whose unique names appear in `hs`, as well as any
hypotheses that depend on them. Returns the number of hypotheses that were
reverted and a list containing these hypotheses. The returned hypotheses are
guaranteed to store the correct type; see `tactic.update_type`.
-/
meta def revert_set (hs : name_set) : tactic (ℕ × list expr) := do
  to_revert ← reverse_dependencies_of_hyps_inclusive' hs,
  to_revert_with_types ← to_revert.mmap update_type,
  num_reverted ← revert_lst to_revert,
  pure (num_reverted, to_revert_with_types)

/--
Revert the local constants in `hs`, as well as any hypotheses that depend on
them. Returns the number of hypotheses that were reverted and a list containing
these hypotheses and their types. The returned hypotheses are
guaranteed to store the correct type; see `tactic.update_type`.
-/
meta def revert_lst' (hs : list expr) : tactic (ℕ × list expr) :=
revert_set $ name_set.of_list $ hs.map expr.local_uniq_name

-- TODO the implementation is a bit of an 'orrible hack
private meta def get_unused_name_reserved_aux (n : name) (reserved : name_set) :
  option nat → tactic name :=
λ suffix, do
  n ← get_unused_name n suffix,
  if ¬ reserved.contains n
    then pure n
    else do
      let new_suffix :=
        match suffix with
        | none := some 1
        | some n := some (n + 1)
        end,
      get_unused_name_reserved_aux new_suffix

meta def get_unused_name_reserved (ns : list name) (reserved : name_set) :
  tactic name := do
  let fallback := match ns with | [] := `x | x :: _ := x end,
  (first $ ns.map $ λ n, do {
    guard (¬ reserved.contains n),
    fail_if_success (resolve_name n),
    pure n
  })
  <|>
  get_unused_name_reserved_aux fallback reserved none

/- Precond: ns is nonempty. -/
meta def intro_fresh_reserved (ns : list name) (reserved : name_set) : tactic expr :=
get_unused_name_reserved ns reserved >>= intro

/- Precond: each of the name lists is nonempty. -/
meta def intro_lst_fresh_reserved (ns : list (name ⊕ list name)) (reserved : name_set) :
  tactic (list expr) := do
  let fixed := name_set.of_list $ ns.filter_map sum.get_left,
  let reserved := reserved.union fixed,
  ns.mmap $ λ spec,
    match spec with
    | sum.inl n := intro n
    | sum.inr ns := intro_fresh_reserved ns reserved
    end

-- TODO integrate into tactic.rename?
-- Precond: each of the name lists in `renames` must be nonempty.
meta def rename_fresh (renames : name_map (list name)) (reserved : name_set) :
  tactic (name_map name) := do
  ctx ← revertible_local_context,
  let ctx_suffix := ctx.drop_while (λ h, (renames.find h.local_pp_name).is_none),
  let new_names :=
    ctx_suffix.map $ λ h,
      match renames.find h.local_pp_name with
      | none := sum.inl h.local_pp_name
      | some new_names := sum.inr new_names
      end,
  revert_lst ctx_suffix,
  new_hyps ← intro_lst_fresh_reserved new_names reserved,
  pure $ rb_map.of_list $
    list.map₂ (λ (old new : expr), (old.local_pp_name, new.local_pp_name))
      ctx_suffix new_hyps

end tactic
