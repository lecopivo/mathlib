/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.noetherian
import ring_theory.ideal.operations
import ring_theory.algebra_tower

/-!
# Finiteness conditions in commutative algebra

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `module.finite`, `algebra.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `algebra.finite_type`, `ring_hom.finite_type`, `alg_hom.finite_type`
  all of these express that some object is finitely generated *as algebra* over some base ring.

-/

open function (surjective)
open_locale big_operators

section module_and_algebra

variables (R A B M N : Type*) [comm_ring R]
variables [comm_ring A] [algebra R A] [comm_ring B] [algebra R B]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]

/-- A module over a commutative ring is `finite` if it is finitely generated as a module. -/
@[class]
def module.finite : Prop := (⊤ : submodule R M).fg

/-- An algebra over a commutative ring is of `finite_type` if it is finitely generated
over the base ring as algebra. -/
@[class]
def algebra.finite_type : Prop := (⊤ : subalgebra R A).fg

namespace module

variables {R M N}
lemma finite_def : finite R M ↔ (⊤ : submodule R M).fg := iff.rfl
variables (R M N)

@[priority 100] -- see Note [lower instance priority]
instance is_noetherian.finite [is_noetherian R M] : finite R M :=
is_noetherian.noetherian ⊤

namespace finite

variables {R M N}

lemma of_surjective [hM : finite R M] (f : M →ₗ[R] N) (hf : surjective f) :
  finite R N :=
by { rw [finite, ← linear_map.range_eq_top.2 hf, ← submodule.map_top], exact submodule.fg_map hM }

lemma of_injective [is_noetherian R N] (f : M →ₗ[R] N)
  (hf : function.injective f) : finite R M :=
fg_of_injective f $ linear_map.ker_eq_bot.2 hf

variables (R)

instance self : finite R R :=
⟨{1}, by simpa only [finset.coe_singleton] using ideal.span_singleton_one⟩

variables {R}

instance prod [hM : finite R M] [hN : finite R N] : finite R (M × N) :=
begin
  rw [finite, ← submodule.prod_top],
  exact submodule.fg_prod hM hN
end

lemma equiv [hM : finite R M] (e : M ≃ₗ[R] N) : finite R N :=
of_surjective (e : M →ₗ[R] N) e.surjective

section algebra

lemma trans [algebra A B] [is_scalar_tower R A B] [hRA : finite R A] [hAB : finite A B] :
  finite R B :=
let ⟨s, hs⟩ := hRA, ⟨t, ht⟩ := hAB in submodule.fg_def.2
⟨set.image2 (•) (↑s : set A) (↑t : set B),
set.finite.image2 _ s.finite_to_set t.finite_to_set,
by rw [set.image2_smul, submodule.span_smul hs (↑t : set B), ht, submodule.restrict_scalars_top]⟩

@[priority 100] -- see Note [lower instance priority]
instance finite_type [hRA : finite R A] : algebra.finite_type R A :=
subalgebra.fg_of_submodule_fg hRA

end algebra

end finite

end module

namespace algebra

namespace finite_type

lemma self : finite_type R R := ⟨{1}, subsingleton.elim _ _⟩

section
open_locale classical

protected lemma mv_polynomial (ι : Type*) [fintype ι] : finite_type R (mv_polynomial ι R) :=
⟨finset.univ.image mv_polynomial.X, begin
  rw eq_top_iff, refine λ p, mv_polynomial.induction_on' p
    (λ u x, finsupp.induction u (subalgebra.algebra_map_mem _ x)
      (λ i n f hif hn ih, _))
    (λ p q ihp ihq, subalgebra.add_mem _ ihp ihq),
  rw [add_comm, mv_polynomial.monomial_add_single],
  exact subalgebra.mul_mem _ ih
    (subalgebra.pow_mem _ (subset_adjoin $ finset.mem_image_of_mem _ $ finset.mem_univ _) _)
end⟩
end

variables {R A B}

lemma of_surjective (hRA : finite_type R A) (f : A →ₐ[R] B) (hf : surjective f) :
  finite_type R B :=
begin
  rw [finite_type] at hRA ⊢,
  convert subalgebra.fg_map _ f hRA,
  simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, alg_hom.mem_range] using hf
end

lemma equiv (hRA : finite_type R A) (e : A ≃ₐ[R] B) : finite_type R B :=
hRA.of_surjective e e.surjective

lemma trans [algebra A B] [is_scalar_tower R A B] (hRA : finite_type R A) (hAB : finite_type A B) :
  finite_type R B :=
fg_trans' hRA hAB

end finite_type

end algebra

end module_and_algebra

namespace ring_hom
variables {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C]

/-- A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def finite (f : A →+* B) : Prop :=
by letI : algebra A B := f.to_algebra; exact module.finite A B

/-- A ring morphism `A →+* B` is of `finite_type` if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →+* B) : Prop := @algebra.finite_type A B _ _ f.to_algebra

namespace finite

variables (A)

lemma id : finite (ring_hom.id A) := module.finite.self A

variables {A}

lemma of_surjective (f : A →+* B) (hf : surjective f) : f.finite :=
begin
  letI := f.to_algebra,
  exact module.finite.of_surjective (algebra.of_id A B).to_linear_map hf
end

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite) (hf : f.finite) : (g.comp f).finite :=
@module.finite.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
begin
  fconstructor,
  intros a b c,
  simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
  refl
end
hf hg

lemma finite_type {f : A →+* B} (hf : f.finite) : finite_type f :=
@module.finite.finite_type _ _ _ _ f.to_algebra hf

end finite

namespace finite_type

variables (A)

lemma id : finite_type (ring_hom.id A) := algebra.finite_type.self A

variables {A}

lemma comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.finite_type) (hg : surjective g) :
  (g.comp f).finite_type :=
@algebra.finite_type.of_surjective A B C _ _ f.to_algebra _ (g.comp f).to_algebra hf
{ to_fun := g, commutes' := λ a, rfl, .. g } hg

lemma of_surjective (f : A →+* B) (hf : surjective f) : f.finite_type :=
by { rw ← f.comp_id, exact (id A).comp_surjective hf }

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite_type) (hf : f.finite_type) :
  (g.comp f).finite_type :=
@algebra.finite_type.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
begin
  fconstructor,
  intros a b c,
  simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
  refl
end
hf hg

end finite_type

end ring_hom

namespace alg_hom

variables {R A B C : Type*} [comm_ring R]
variables [comm_ring A] [comm_ring B] [comm_ring C]
variables [algebra R A] [algebra R B] [algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def finite (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite

/-- An algebra morphism `A →ₐ[R] B` is of `finite_type` if it is of finite type as ring morphism.
In other words, if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite_type

namespace finite

variables (R A)

lemma id : finite (alg_hom.id R A) := ring_hom.finite.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite) (hf : f.finite) : (g.comp f).finite :=
ring_hom.finite.comp hg hf

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite :=
ring_hom.finite.of_surjective f hf

lemma finite_type {f : A →ₐ[R] B} (hf : f.finite) : finite_type f :=
ring_hom.finite.finite_type hf

end finite

namespace finite_type

variables (R A)

lemma id : finite_type (alg_hom.id R A) := ring_hom.finite_type.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite_type) (hf : f.finite_type) :
  (g.comp f).finite_type :=
ring_hom.finite_type.comp hg hf

lemma comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.finite_type) (hg : surjective g) :
  (g.comp f).finite_type :=
ring_hom.finite_type.comp_surjective hf hg

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite_type :=
ring_hom.finite_type.of_surjective f hf

end finite_type

end alg_hom
