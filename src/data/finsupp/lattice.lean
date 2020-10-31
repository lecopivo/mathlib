/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.finsupp.basic
import algebra.ordered_group

/-!
# Lattice structure on finsupps

This file provides instances of ordered structures on finsupps.

-/

open_locale classical
noncomputable theory
variables {α : Type*} {β : Type*} [has_zero β] {μ : Type*} [canonically_ordered_add_monoid μ]
variables {γ : Type*} [canonically_linear_ordered_add_monoid γ]

namespace finsupp

lemma le_def [partial_order β] {a b : α →₀ β} : a ≤ b ↔ ∀ (s : α), a s ≤ b s := by refl

instance : order_bot (α →₀ μ) :=
{ bot := 0, bot_le := by simp [finsupp.le_def, ← bot_eq_zero], .. finsupp.partial_order}

instance [semilattice_inf β] : semilattice_inf (α →₀ β) :=
{ inf := zip_with (⊓) inf_idem,
  inf_le_left := λ a b c, inf_le_left,
  inf_le_right := λ a b c, inf_le_right,
  le_inf := λ a b c h1 h2 s, le_inf (h1 s) (h2 s),
  ..finsupp.partial_order, }

@[simp]
lemma inf_apply [semilattice_inf β] {a : α} {f g : α →₀ β} : (f ⊓ g) a = f a ⊓ g a := rfl

@[simp]
lemma support_inf {f g : α →₀ γ} : (f ⊓ g).support = f.support ∩ g.support :=
begin
  ext, simp only [inf_apply, mem_support_iff,  ne.def,
    finset.mem_union, finset.mem_filter, finset.mem_inter],
  rw [← decidable.not_or_iff_and_not, ← not_congr],
  rw inf_eq_min, unfold min, split_ifs;
  { try {apply or_iff_left_of_imp}, try {apply or_iff_right_of_imp}, intro con, rw con at h,
    revert h, simp, }
end

instance [semilattice_sup β] : semilattice_sup (α →₀ β) :=
{ sup := zip_with (⊔) sup_idem,
  le_sup_left := λ a b c, le_sup_left,
  le_sup_right := λ a b c, le_sup_right,
  sup_le := λ a b c h1 h2 s, sup_le (h1 s) (h2 s),
  ..finsupp.partial_order, }

@[simp]
lemma sup_apply [semilattice_sup β] {a : α} {f g : α →₀ β} : (f ⊔ g) a = f a ⊔ g a := rfl

@[simp]
lemma support_sup
  {f g : α →₀ γ} : (f ⊔ g).support = f.support ∪ g.support :=
begin
  ext, simp only [finset.mem_union, mem_support_iff, sup_apply, ne.def, ← bot_eq_zero],
  rw sup_eq_bot_iff, tauto,
end

instance lattice [lattice β] : lattice (α →₀ β) :=
{ .. finsupp.semilattice_inf, .. finsupp.semilattice_sup}

instance semilattice_inf_bot : semilattice_inf_bot (α →₀ γ) :=
{ ..finsupp.order_bot, ..finsupp.lattice}

lemma of_multiset_strict_mono : strict_mono (@finsupp.of_multiset α) :=
begin
  unfold strict_mono, intros a b hab, rw lt_iff_le_and_ne at *, split,
  { rw finsupp.le_iff, intros s hs, repeat {rw finsupp.of_multiset_apply},
    rw multiset.le_iff_count at hab, apply hab.left },
  { have h := hab.right, contrapose h, simp at *,
    apply finsupp.equiv_multiset.symm.injective h }
end

lemma bot_eq_zero : (⊥ : α →₀ γ) = 0 := rfl

lemma disjoint_iff {x y : α →₀ γ} : disjoint x y ↔ disjoint x.support y.support :=
begin
  unfold disjoint, repeat {rw le_bot_iff},
  rw [finsupp.bot_eq_zero, ← finsupp.support_eq_empty, finsupp.support_inf], refl,
end

/-- The lattice of `finsupp`s to `ℕ` is order-isomorphic to that of `multiset`s.  -/
def order_iso_multiset :
  (α →₀ ℕ) ≃o multiset α :=
⟨finsupp.equiv_multiset, begin
  intros a b, unfold finsupp.equiv_multiset, dsimp,
  rw multiset.le_iff_count, simp only [finsupp.count_to_multiset], refl
end ⟩

@[simp] lemma order_iso_multiset_apply {f : α →₀ ℕ} : order_iso_multiset f = f.to_multiset := rfl

@[simp] lemma order_iso_multiset_symm_apply {s : multiset α} :
  order_iso_multiset.symm s = s.to_finsupp :=
by { conv_rhs { rw ← (rel_iso.apply_symm_apply order_iso_multiset) s}, simp }

variable [partial_order β]

/-- The order on `finsupp`s over a partial order embeds into the order on functions -/
def order_embedding_to_fun :
  (α →₀ β) ↪o (α → β) :=
⟨⟨λ (f : α →₀ β) (a : α), f a,  λ f g h, finsupp.ext (λ a, by { dsimp at h, rw h,} )⟩,
  λ a b, le_def⟩

@[simp] lemma order_embedding_to_fun_apply {f : α →₀ β} {a : α} :
  order_embedding_to_fun f a = f a := rfl

lemma monotone_to_fun : monotone (finsupp.to_fun : (α →₀ β) → (α → β)) := λ f g h a, le_def.1 h a

end finsupp
