import analysis.convenient_space.smooth_map

reserve infixr ` ⊸ `:25

namespace convenient


  --  ___                _   _      _    _                     __  __
  -- / __|_ __  ___  ___| |_| |_   | |  (_)_ _  ___ __ _ _ _  |  \/  |__ _ _ __
  -- \__ \ '  \/ _ \/ _ \  _| ' \  | |__| | ' \/ -_) _` | '_| | |\/| / _` | '_ \
  -- |___/_|_|_\___/\___/\__|_||_| |____|_|_||_\___\__,_|_|   |_|  |_\__,_| .__/
  --                                                                      |_|
  structure smooth_linear_map (E : Type*) (F : Type*)
    [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
    [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
    extends smooth_map E F:=
    ( linearity : is_linear_map ℝ to_fun )

  notation E ` ⊸ ` F := smooth_linear_map E F

  namespace smooth_linear_map

    section function_space_basics
      variables 
        {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
        {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
  
      /-- Coerce smooth linear maps to smooth maps. -/
      instance : has_coe (E⊸F) (E⟿F) := ⟨to_smooth_map⟩
  
      /-- Coerce smooth linear maps to functions. -/
      -- see Note [function coercion]
      instance to_fun : has_coe_to_fun (E ⊸ F) := ⟨λ _, E → F, λ f, f⟩
  
      @[simp] lemma coe_mk (f : E ⟿ F) (h) : (mk f h : E ⟿ F) = f := rfl
      @[simp] lemma coe_mk' (f : E ⟿ F) (h) : (mk f h : E → F) = f := rfl
      @[simp] lemma to_smooth_map_eq_coe (f : E⊸F) : f.1 = (f : E ⟿ F) := rfl
  
      /- TODO: This will be usefull once I have tactics proving smoothness and linearity -/
      -- @[smoothness]
      -- protected lemma is_smooth (f : E ⊸ F) : is_smooth f := f.1.2
  
      -- @[linearity]
      -- protected lemma is_linear (f : E ⊸ F) : is_linear_map ℝ f := f.2
  
      theorem coe_injective : function.injective (coe : (E ⊸ F) → (E ⟿ F)) :=
      by { intros f g H, cases f, cases g, congr' 1, exact H }
  
      theorem injective_coe_fn : function.injective (λ f : E ⊸ F, show E → F, from f) :=
      smooth_map.coe_injective.comp coe_injective
  
      @[ext] theorem ext {f g : E⊸F} (h : ∀ x, f x = g x) : f = g :=
        injective_coe_fn $ funext h
  
      theorem ext_iff {f g : E⊸F} : f = g ↔ ∀ x, f x = g x :=
        ⟨λ h x, by rw h, by ext⟩    

      @[simp, norm_cast] lemma coe_coe (f : E⊸F) : ((f : E ⟿ F) : (E → F)) = (f : E → F) := rfl

      variables (s : ℝ) (f g : E⊸F) (x y z : E)

      -- make some straightforward lemmas available to `simp`.
      @[simp] lemma map_add  : f (x + y) = f x + f y := by apply f.2.1
      @[simp] lemma map_smul : f (s • x) = s • f x := by apply f.2.2
      @[simp] lemma map_zero : f (0 : E) = 0 := begin transitivity f ((0 : ℝ) • (0 : E)), simp, rw map_smul, simp, end

    end function_space_basics

    section composition
      variables 
        {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
        {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
        {G : Type*} [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G]
        (f : F⊸G) (g : E⊸F)

      /-- Composition of two smooth maps is a smoth map -/
      def comp : E ⊸ G := mk (smooth_map.comp f.to_smooth_map g.to_smooth_map) (begin split, repeat {intros, simp}, end)

      @[simp] lemma comp_apply (x : E) : comp f g x = f (g x) := rfl

      @[norm_cast]
      lemma comp_coe : (f : F → G) ∘ (g : E → F) = f.comp g := rfl
    end composition


    --    _   _          _
    --   /_\ | |__ _ ___| |__ _ _ __ _
    --  / _ \| / _` / -_) '_ \ '_/ _` |
    -- /_/ \_\_\__, \___|_.__/_| \__,_|
    --         |___/
    section algebra
      variables 
        {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
        {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 

      instance : has_add (E⊸F) := 
        has_add.mk (λ (f g : E⊸F), ⟨f.1 + g.1, begin split, intros, simp, abel, intros, simp, rw smul_add, end ⟩)

      instance : has_zero (E⊸F) := 
        has_zero.mk ⟨(0 : E⟿F), begin split, intros, simp, intros, simp, end⟩

      instance : has_neg (E⊸F) := 
        has_neg.mk (λ f, ⟨-f.1, begin split, intros, simp, abel, intros, simp, end⟩)

      noncomputable
      instance : has_scalar ℝ (E⊸F) := 
        has_scalar.mk (λ s f, ⟨s • f.1, begin split, intros, simp, rw smul_add, intros, simp, repeat {rw smul_smul}, rw mul_comm, end⟩)

      variables {f g : E⊸F} {x : E} {s : ℝ}

      @[simp] lemma add_apply  : (f + g) x = f x + g x := rfl
      @[simp] lemma zero_apply : (0 : E⊸F) x = (0 : F) := rfl
      @[simp] lemma neg_apply  : (-f) x = - (f x) := rfl
      @[simp] lemma smul_apply  : (s • f) x = s • (f x) := rfl

      instance : add_comm_group (E⊸F) :=
        add_comm_group.mk 
          /- add -/ 
          (has_add.add)
          (begin intros, ext, simp, abel, end)
          /- zero -/ 
          (has_zero.zero) 
          (begin intros, ext, rw add_apply, rw zero_apply, simp, end) /- simp fucks it up here for some reason ... -/
          (begin intros, ext, rw add_apply, rw zero_apply, simp, end) /- so it has to be done manualy -/
          /- neg -/ 
          (has_neg.neg)
          (begin intros, ext, simp, end) 
          /- commutativity of add -/
          (begin intros, ext, simp, abel, end)

    /- Mul Action -/
    noncomputable instance : mul_action ℝ (E⊸F) :=  
      mul_action.mk 
        (begin intros, ext, simp, end)
        (begin intros, ext, simp, rw mul_smul, end)

    /- Distrib Mul Action -/
    noncomputable instance : distrib_mul_action ℝ (E⊸F) := 
      distrib_mul_action.mk 
        (begin intros, ext, simp, rw smul_add, end)
        (begin intros, ext, simp,  end)

    /- Semimodule -/
    noncomputable instance : semimodule ℝ (E⊸F) := 
      semimodule.mk 
         (begin intros, ext, simp, rw add_smul, end)
         (begin intros, ext, simp,  end)

    end algebra 


    section topology
      variables 
        {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
        {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
  
      instance : topological_space (E⊸F) := topological_space.induced (coe : (E⊸F)→(E⟿F)) (by apply_instance)

      instance : locally_convex_space ℝ (E⟿F) := {seminorms_induce_topology := sorry }

    end topology

  end smooth_linear_map



end convenient
