import analysis.convenient_space.curve

reserve infixr ` ⟿ `:25

namespace convenient

  --  ___      ___                _   _
  -- |_ _|___ / __|_ __  ___  ___| |_| |_
  --  | |(_-< \__ \ '  \/ _ \/ _ \  _| ' \
  -- |___/__/ |___/_|_|_\___/\___/\__|_||_|
  /- for simplicity we consider only infinite differentiability now -/
  section is_smooth
    variables 
      {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E] 
      {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F]

    def is_smooth_on (f : E → F)  (U : set E)  : Prop :=
      ∀ (c : smooth_curve E), (∀ t, (c t) ∈ U) → curve.is_smooth (f∘c)
    @[reducible]
    def is_smooth (f : E → F) : Prop := is_smooth_on f ⊤
      
    lemma zero.is_smooth_on (U : set E) : is_smooth_on (0 : E → F) U := sorry
    lemma add.is_smooth_on (U : set E) (f g : E → F) : 
      (is_smooth_on f U) → (is_smooth_on g U) → (is_smooth_on (f+g) U) := sorry
    lemma smul.is_smooth_on (U : set E) (s : ℝ) (f : E → F) : 
      (is_smooth_on f U) → (is_smooth_on (s•f) U) := sorry
    lemma neg.is_smooth_on (U : set E) (f : E → F) : 
      (is_smooth_on f U) → (is_smooth_on (-f) U) := sorry

    variables
      {G : Type*} [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G]

    lemma comp.is_smooth (f : F→G) (g : E→F) : 
      (is_smooth f) → (is_smooth g) → (is_smooth (f∘g)) := sorry
    
    
  end is_smooth

  --  ___                _   _      __  __
  -- / __|_ __  ___  ___| |_| |_   |  \/  |__ _ _ __
  -- \__ \ '  \/ _ \/ _ \  _| ' \  | |\/| / _` | '_ \
  -- |___/_|_|_\___/\___/\__|_||_| |_|  |_\__,_| .__/
  --                                           |_|
  /- for simplicity we consider only infinitely differentiable maps, defined over the whole source vector space -/
  structure smooth_map (E : Type*) (F : Type*)
   [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
   [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] :=
   ( to_fun : E→F )
   ( is_smooth : is_smooth to_fun)

   /- First I was thinking defining it as a submodule but this automatically induces topology on E⟿F that is however not the one that should be used! -/
   -- submodule.mk ((λ f, is_smooth_on f ⊤) : set (E→F)) 
   --   (zero.is_smooth_on ⊤) 
   --   (add.is_smooth_on ⊤) 
   --   (smul.is_nsmooth_on ⊤)

  notation E ` ⟿ ` F := smooth_map E F

  namespace smooth_map

    section function_space_basics
      variables 
        {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
        {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
  
      instance  : has_coe_to_fun (E⟿F) := has_coe_to_fun.mk _ smooth_map.to_fun
  
      @[simp] lemma to_fun_eq_coe (f : E⟿F ) : f.to_fun = ⇑f := rfl
  
      variables {f g : E⟿F}
  
      theorem coe_injective : function.injective (λ f : E⟿F, show E→F, from f) :=
        by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr
  
      @[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
      coe_injective $ funext H
  
      protected lemma congr_arg : Π {x x' : E}, x = x' → f x = f x'
      | _ _ rfl := rfl
  
      /-- If two linear maps are equal, they are equal at each point. -/
      protected lemma congr_fun (h : f = g) (x : E) : f x = g x := h ▸ rfl
  
      theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
      ⟨by { rintro rfl x, refl }, ext⟩

    end function_space_basics

    section composition
      variables 
        {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
        {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
        {G : Type*} [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G]
        (f : F⟿G) (g : E⟿F)

      /-- Composition of two smooth maps is a smoth map -/
      def comp : E ⟿ G := ⟨f ∘ g, begin apply comp.is_smooth, apply f.2, apply g.2 end ⟩

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

      instance : has_add (E⟿F) := 
        has_add.mk (λ (f g : E⟿F), ⟨λ x, f x + g x, begin apply add.is_smooth_on ⊤, apply f.2, apply g.2 end⟩)

      instance : has_zero (E⟿F) := 
        has_zero.mk ⟨λ x, (0 : F), zero.is_smooth_on ⊤⟩ 

      instance : has_neg (E⟿F) := 
        has_neg.mk (λ f, ⟨λ x, - (f x), begin apply neg.is_smooth_on ⊤, apply f.2, end⟩)

      noncomputable
      instance : has_scalar ℝ (E⟿F) := 
        has_scalar.mk (λ s f, ⟨λ x, s • (f x), begin apply smul.is_smooth_on ⊤, apply f.2,  end ⟩)

      variables {f g : E⟿F} {x : E} {s : ℝ}

      @[simp] lemma add_apply  : (f + g) x = f x + g x := rfl
      @[simp] lemma zero_apply : (0 : E⟿F) x = (0 : F) := rfl
      @[simp] lemma neg_apply  : (-f) x = - (f x) := rfl
      @[simp] lemma smul_apply  : (s • f) x = s • (f x) := rfl

      instance : add_comm_group (E⟿F) :=
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
    noncomputable instance : mul_action ℝ (E⟿F) :=  
      mul_action.mk 
        (begin intros, ext, simp, end)
        (begin intros, ext, simp, rw mul_smul, end)

    /- Distrib Mul Action -/
    noncomputable instance : distrib_mul_action ℝ (E⟿F) := 
      distrib_mul_action.mk 
        (begin intros, ext, simp, rw smul_add, end)
        (begin intros, ext, simp,  end)

    /- Semimodule -/
    noncomputable instance : semimodule ℝ (E⟿F) := 
      semimodule.mk 
         (begin intros, ext, simp, rw add_smul, end)
         (begin intros, ext, simp,  end)

    end algebra 

    --  _____              _
    -- |_   _|__ _ __  ___| |___  __ _ _  _
    --   | |/ _ \ '_ \/ _ \ / _ \/ _` | || |
    --   |_|\___/ .__/\___/_\___/\__, |\_, |
    --          |_|              |___/ |__/
    section topology
      variables 
        {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
        {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
  
      instance : topological_space (E⟿F) := 
        ⨅(c : smooth_curve E), topological_space.induced (λ f : (E⟿F), (⟨f∘c, f.2 c (by tauto)⟩ : smooth_curve F)) (by apply_instance)

      instance : locally_convex_space ℝ (E⟿F) := {seminorms_induce_topology := sorry }
    
    end topology
    
  end smooth_map


end convenient
