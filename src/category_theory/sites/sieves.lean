/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/

import category_theory.over
import category_theory.limits.shapes.finite_limits
import category_theory.yoneda
import order.complete_lattice
import data.set.lattice

/-!
# Theory of sieves

- For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X`
  which is closed under left-composition.
- The complete lattice structure on sieves is given, as well as the Galois insertion
  given by downward-closing.
- A `sieve X` (functorially) induces a presheaf on `C` together with a monomorphism to
  the yoneda embedding of `X`.

## Tags

sieve, pullback
-/

universes v u
namespace category_theory

variables {C : Type u} [category.{v} C]
variables {X Y Z : C} (f : Y ⟶ X)

/-- A set of arrows all with codomain `X`. -/
@[derive complete_lattice]
def presieve (X : C) := Π ⦃Y⦄, set (Y ⟶ X)

namespace presieve

instance : inhabited (presieve X) := ⟨⊤⟩

/--
Given a set of arrows `S` all with codomain `X`, and a set of arrows with codomain `Y` for each
`f : Y ⟶ X` in `S`, produce a set of arrows with codomain `X`:
`{ g ≫ f | (f : Y ⟶ X) ∈ S, (g : Z ⟶ Y) ∈ R f }`.
-/
def bind (S : presieve X) (R : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → presieve Y) :
  presieve X :=
λ Z h, ∃ (Y : C) (g : Z ⟶ Y) (f : Y ⟶ X) (H : S f), R H g ∧ g ≫ f = h

@[simp]
lemma bind_comp {S : presieve X}
  {R : Π ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → presieve Y} {g : Z ⟶ Y} (h₁ : S f) (h₂ : R h₁ g) :
bind S R (g ≫ f) :=
⟨_, _, _, h₁, h₂, rfl⟩

/-- The singleton presieve.  -/
-- Note we can't make this into `has_singleton` because of the out-param.
def singleton : presieve X :=
λ Z g, ∃ (H : Z = Y), eq_to_hom H ≫ f = g

@[simp] lemma singleton_eq_iff_domain (f g : Y ⟶ X) : singleton f g ↔ f = g :=
begin
  split,
  { rintro ⟨_, rfl⟩,
    apply (category.id_comp _).symm },
  { rintro rfl,
    exact ⟨rfl, category.id_comp _⟩ },
end

lemma singleton_arrow_self : singleton f f := (singleton_eq_iff_domain _ _).2 rfl

end presieve

/--
For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X` which is closed under
left-composition.
-/
structure sieve {C : Type u} [category.{v} C] (X : C) :=
(arrows : presieve X)
(downward_closed' : ∀ {Y Z f} (hf : arrows f) (g : Z ⟶ Y), arrows (g ≫ f))

namespace sieve

instance {X : C} : has_coe_to_fun (sieve X) := ⟨_, sieve.arrows⟩

variables {S R : sieve X}

@[simp, priority 100] lemma downward_closed (S : sieve X) {f : Y ⟶ X} (hf : S f)
  (g : Z ⟶ Y) : S (g ≫ f) :=
S.downward_closed' hf g

lemma arrows_ext : Π {R S : sieve X}, R.arrows = S.arrows → R = S
| ⟨Ra, _⟩ ⟨Sa, _⟩ rfl := rfl

@[ext]
protected lemma ext {R S : sieve X}
  (h : ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) :
  R = S :=
arrows_ext $ funext $ λ x, funext $ λ f, propext $ h f

protected lemma ext_iff {R S : sieve X} :
  R = S ↔ (∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) :=
⟨λ h Y f, h ▸ iff.rfl, sieve.ext⟩

open lattice

/-- The supremum of a collection of sieves: the union of them all. -/
protected def Sup (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := λ Y, {f | ∃ S ∈ 𝒮, sieve.arrows S f},
  downward_closed' := λ Y Z f, by { rintro ⟨S, hS, hf⟩ g, exact ⟨S, hS, S.downward_closed hf _⟩ } }

/-- The infimum of a collection of sieves: the intersection of them all. -/
protected def Inf (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := λ Y, {f | ∀ S ∈ 𝒮, sieve.arrows S f},
  downward_closed' := λ Y Z f hf g S H, S.downward_closed (hf S H) g }

/-- The union of two sieves is a sieve. -/
protected def union (S R : sieve X) : sieve X :=
{ arrows := λ Y f, S f ∨ R f,
  downward_closed' := by { rintros Y Z f (h | h) g; simp [h] } }

/-- The intersection of two sieves is a sieve. -/
protected def inter (S R : sieve X) : sieve X :=
{ arrows := λ Y f, S f ∧ R f,
  downward_closed' := by { rintros Y Z f ⟨h₁, h₂⟩ g, simp [h₁, h₂] } }

/--
Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the galois insertion for nicer definitional properties.
-/
instance : complete_lattice (sieve X) :=
{ le           := λ S R, ∀ ⦃Y⦄ (f : Y ⟶ X), S f → R f,
  le_refl      := λ S f q, id,
  le_trans     := λ S₁ S₂ S₃ S₁₂ S₂₃ Y f h, S₂₃ _ (S₁₂ _ h),
  le_antisymm  := λ S R p q, sieve.ext (λ Y f, ⟨p _, q _⟩),
  top          := { arrows := λ _, set.univ, downward_closed' := λ Y Z f g h, ⟨⟩ },
  bot          := { arrows := λ _, ∅, downward_closed' := λ _ _ _ p _, false.elim p },
  sup          := sieve.union,
  inf          := sieve.inter,
  Sup          := sieve.Sup,
  Inf          := sieve.Inf,
  le_Sup       := λ 𝒮 S hS Y f hf, ⟨S, hS, hf⟩,
  Sup_le       := λ ℰ S hS Y f, by { rintro ⟨R, hR, hf⟩, apply hS R hR _ hf },
  Inf_le       := λ _ _ hS _ _ h, h _ hS,
  le_Inf       := λ _ _ hS _ _ hf _ hR, hS _ hR _ hf,
  le_sup_left  := λ _ _ _ _, or.inl,
  le_sup_right := λ _ _ _ _, or.inr,
  sup_le       := λ _ _ _ a b _ _ hf, hf.elim (a _) (b _),
  inf_le_left  := λ _ _ _ _, and.left,
  inf_le_right := λ _ _ _ _, and.right,
  le_inf       := λ _ _ _ p q _ _ z, ⟨p _ z, q _ z⟩,
  le_top       := λ _ _ _ _, trivial,
  bot_le       := λ _ _ _, false.elim }

/-- The maximal sieve always exists. -/
instance sieve_inhabited : inhabited (sieve X) := ⟨⊤⟩

@[simp]
lemma mem_Inf {Ss : set (sieve X)} {Y} (f : Y ⟶ X) :
  Inf Ss f ↔ ∀ (S : sieve X) (H : S ∈ Ss), S f :=
iff.rfl

@[simp]
lemma mem_Sup {Ss : set (sieve X)} {Y} (f : Y ⟶ X) :
  Sup Ss f ↔ ∃ (S : sieve X) (H : S ∈ Ss), S f :=
iff.rfl

@[simp]
lemma mem_inter {R S : sieve X} {Y} (f : Y ⟶ X) :
  (R ⊓ S) f ↔ R f ∧ S f :=
iff.rfl

@[simp]
lemma mem_union {R S : sieve X} {Y} (f : Y ⟶ X) :
  (R ⊔ S) f ↔ R f ∨ S f :=
iff.rfl

@[simp]
lemma mem_top (f : Y ⟶ X) : (⊤ : sieve X) f := trivial

/-- Generate the smallest sieve containing the given set of arrows. -/
def generate (R : presieve X) : sieve X :=
{ arrows := λ Z f, ∃ Y (h : Z ⟶ Y) (g : Y ⟶ X), R g ∧ h ≫ g = f,
  downward_closed' :=
  begin
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h,
    exact ⟨_, h ≫ g, _, hf, by simp⟩,
  end }

lemma mem_generate (R : presieve X) (f : Z ⟶ X) :
  generate R f ↔ ∃ (Y : C) (h : Z ⟶ Y) (g : Y ⟶ X), R g ∧ h ≫ g = f :=
iff.rfl

/-- Given a collection of arrows with fixed codomain,  -/
def bind (S : presieve X) (R : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → sieve Y) : sieve X :=
{ arrows := S.bind (λ Y f h, R h),
  downward_closed' :=
  begin
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g,
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩,
  end }

open order lattice

lemma sets_iff_generate (R : presieve X) (S : sieve X) :
  generate R ≤ S ↔ R ≤ S :=
⟨λ H Y g hg, H _ ⟨_, 𝟙 _, _, hg, category.id_comp _⟩,
 λ ss Y f,
  begin
    rintro ⟨Z, f, g, hg, rfl⟩,
    exact S.downward_closed (ss Z hg) f,
  end⟩

/-- Show that there is a galois insertion (generate, set_over). -/
def gi_generate : galois_insertion (generate : presieve X → sieve X) arrows :=
{ gc := sets_iff_generate,
  choice := λ 𝒢 _, generate 𝒢,
  choice_eq := λ _ _, rfl,
  le_l_u := λ S Y f hf, ⟨_, 𝟙 _, _, hf, category.id_comp _⟩ }

/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
    as the inverse image of S with `_ ≫ h`.
    That is, `sieve.pullback S h := (≫ h) '⁻¹ S`. -/
def pullback (h : Y ⟶ X) (S : sieve X) : sieve Y :=
{ arrows := λ Y sl, S (sl ≫ h),
  downward_closed' := λ Z W f g h, by simp [g] }

@[simp] lemma mem_pullback (h : Y ⟶ X) {f : Z ⟶ Y} :
  (S.pullback h) f ↔ S (f ≫ h) := iff.rfl

@[simp]
lemma pullback_id : S.pullback (𝟙 _) = S :=
by simp [sieve.ext_iff]

@[simp]
lemma pullback_top {f : Y ⟶ X} : (⊤ : sieve X).pullback f = ⊤ :=
top_unique (λ _ g, id)

lemma pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : sieve X) :
  S.pullback (g ≫ f) = (S.pullback f).pullback g :=
by simp [sieve.ext_iff]

@[simp]
lemma pullback_inter {f : Y ⟶ X} (S R : sieve X) :
 (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f :=
by simp [sieve.ext_iff]

/-- If the identity arrow is in a sieve, the sieve is maximal. -/
lemma id_mem_iff_eq_top : S (𝟙 X) ↔ S = ⊤ :=
⟨λ h, top_unique $ λ Y f _, by simpa using downward_closed _ h f,
 λ h, h.symm ▸ trivial⟩

lemma pullback_eq_top_iff_mem (f : Y ⟶ X) : S f ↔ S.pullback f = ⊤ :=
by rw [← id_mem_iff_eq_top, mem_pullback, category.id_comp]

lemma pullback_eq_top_of_mem (S : sieve X) {f : Y ⟶ X} : S f → S.pullback f = ⊤ :=
(pullback_eq_top_iff_mem f).1

/--
Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X` is in the sieve if `gf`
factors through some `g : Z ⟶ Y` which is in `R`.
-/
def pushforward (f : Y ⟶ X) (R : sieve Y) : sieve X :=
{ arrows := λ Z gf, ∃ g, g ≫ f = gf ∧ R g,
  downward_closed' := λ Z₁ Z₂ g ⟨j, k, z⟩ h, ⟨h ≫ j, by simp [k], by simp [z]⟩ }

@[simp]
lemma mem_pushforward_of_comp {R : sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X) :
  R.pushforward f (g ≫ f) :=
⟨g, rfl, hg⟩

lemma pushforward_comp {f : Y ⟶ X} {g : Z ⟶ Y} (R : sieve Z) :
  R.pushforward (g ≫ f) = (R.pushforward g).pushforward f :=
sieve.ext (λ W h, ⟨λ ⟨f₁, hq, hf₁⟩, ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩,
                   λ ⟨y, hy, z, hR, hz⟩, ⟨z, by rwa reassoc_of hR, hz⟩⟩)

lemma galois_connection (f : Y ⟶ X) : galois_connection (sieve.pushforward f) (sieve.pullback f) :=
λ S R, ⟨λ hR Z g hg, hR _ ⟨g, rfl, hg⟩, λ hS Z g ⟨h, hg, hh⟩, hg ▸ hS h hh⟩

lemma pullback_monotone (f : Y ⟶ X) : monotone (sieve.pullback f) :=
(galois_connection f).monotone_u

lemma pushforward_monotone (f : Y ⟶ X) : monotone (sieve.pushforward f) :=
(galois_connection f).monotone_l

lemma le_pushforward_pullback (f : Y ⟶ X) (R : sieve Y) :
  R ≤ (R.pushforward f).pullback f :=
(galois_connection f).le_u_l _

lemma pullback_pushforward_le (f : Y ⟶ X) (R : sieve X) :
  (R.pullback f).pushforward f ≤ R :=
(galois_connection f).l_u_le _

lemma pushforward_union {f : Y ⟶ X} (S R : sieve Y) :
  (S ⊔ R).pushforward f = S.pushforward f ⊔ R.pushforward f :=
(galois_connection f).l_sup

lemma pushforward_le_bind_of_mem (S : presieve X)
  (R : Π ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → sieve Y) (f : Y ⟶ X) (h : S f) :
  (R h).pushforward f ≤ bind S R :=
begin
  rintro Z _ ⟨g, rfl, hg⟩,
  exact ⟨_, g, f, h, hg, rfl⟩,
end

lemma le_pullback_bind (S : presieve X) (R : Π ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → sieve Y)
  (f : Y ⟶ X) (h : S f) :
  R h ≤ (bind S R).pullback f :=
begin
  rw ← galois_connection f,
  apply pushforward_le_bind_of_mem,
end

/-- If `f` is a monomorphism, the pushforward-pullback adjunction on sieves is coreflective. -/
def galois_coinsertion_of_mono (f : Y ⟶ X) [mono f] :
  galois_coinsertion (sieve.pushforward f) (sieve.pullback f) :=
begin
  apply (galois_connection f).to_galois_coinsertion,
  rintros S Z g ⟨g₁, hf, hg₁⟩,
  rw cancel_mono f at hf,
  rwa ← hf,
end

/-- If `f` is a split epi, the pushforward-pullback adjunction on sieves is reflective. -/
def galois_insertion_of_split_epi (f : Y ⟶ X) [split_epi f] :
  galois_insertion (sieve.pushforward f) (sieve.pullback f) :=
begin
  apply (galois_connection f).to_galois_insertion,
  intros S Z g hg,
  refine ⟨g ≫ section_ f, by simpa⟩,
end

/-- A sieve induces a presheaf. -/
@[simps]
def functor (S : sieve X) : Cᵒᵖ ⥤ Type v :=
{ obj := λ Y, {g : Y.unop ⟶ X // S.arrows g},
  map := λ Y Z f g, ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩ }

/--
If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
@[simps]
def nat_trans_of_le {S T : sieve X} (h : S ≤ T) : S.functor ⟶ T.functor :=
{ app := λ Y f, ⟨f.1, h _ f.2⟩ }.

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
def functor_inclusion (S : sieve X) : S.functor ⟶ yoneda.obj X :=
{ app := λ Y f, f.1 }.

lemma nat_trans_of_le_comm {S T : sieve X} (h : S ≤ T) :
  nat_trans_of_le h ≫ functor_inclusion _ = functor_inclusion _ :=
rfl

/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance functor_inclusion_is_mono : mono (functor_inclusion S) :=
⟨λ Z f g h, by { ext Y y, apply congr_fun (nat_trans.congr_app h Y) y }⟩

end sieve
end category_theory
