import analysis.convenient_space.smooth_map


namespace convenient

  /- The namespace space smooth containes couple usefull smooth functions -/
  namespace smooth
    variables 
      {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
      {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
      {G : Type*} [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G] 

    namespace detail

      /- Identity -/
      lemma id'.is_smooth : is_smooth (@id E) := sorry
      @[reducible] def id' : E⟿E := ⟨id, id'.is_smooth⟩

      /- Comp -/
      lemma comp'''.is_smooth (f : F⟿G) (g : E⟿F) : is_smooth (λ x, f (g x)) := sorry
      @[reducible] def comp''' (f : F⟿G) (g : E⟿F) : E⟿G := ⟨λ x, f (g x), comp'''.is_smooth f g⟩
      
      lemma comp''.is_smooth (f : F⟿G) : is_smooth (comp''' f : (E⟿F)→(E⟿G)) := sorry
      @[reducible] noncomputable def comp'' (f : F⟿G) : (E⟿F)⟿(E⟿G) := ⟨comp''' f, comp''.is_smooth f⟩

      lemma comp'.is_smooth : is_smooth (comp'' : (F⟿G)→(E⟿F)⟿(E⟿G)) := sorry
      @[reducible] noncomputable def comp' : (F⟿G)⟿(E⟿F)⟿(E⟿G) := ⟨comp'', comp'.is_smooth⟩

      /- Curry -/
      lemma curry'''.is_smooth (f : E×F⟿G) (x : E) : is_smooth (λ y : F, f (x,y)) := sorry
      @[reducible] noncomputable def curry''' (f : E×F⟿G) (x : E) : F⟿G := ⟨λ y : F, f (x,y), curry'''.is_smooth f x⟩

      lemma curry''.is_smooth (f : E×F⟿G) : is_smooth (curry''' f) := sorry
      @[reducible] noncomputable def curry'' (f : E×F⟿G) : E⟿F⟿G := ⟨curry''' f, curry''.is_smooth f⟩

      lemma curry'.is_smooth : is_smooth (curry'' : (E×F⟿G)→(E⟿F⟿G)) := sorry
      @[reducible] noncomputable def curry' : (E×F⟿G)⟿(E⟿F⟿G) := ⟨curry'', curry'.is_smooth⟩

      /- Uncurry -/
      lemma uncurry''.is_smooth (f : E⟿F⟿G) : is_smooth (λ p : E×F, f p.1 p.2) := sorry
      @[reducible] noncomputable def uncurry'' (f : E⟿F⟿G) : E×F⟿G := ⟨λ p, f p.1 p.2, uncurry''.is_smooth f⟩

      lemma uncurry'.is_smooth : is_smooth (uncurry'' : (E⟿F⟿G)→(E×F⟿G)) := sorry
      @[reducible] noncomputable def uncurry' : (E⟿F⟿G)⟿(E×F⟿G) := ⟨uncurry'', uncurry'.is_smooth⟩

    end detail

    def id : E⟿E := detail.id'
    noncomputable def comp : (F⟿G)⟿(E⟿F)⟿(E⟿G) := detail.comp'
    noncomputable def curry : (E×F⟿G)⟿(E⟿F⟿G) := detail.curry'
    noncomputable def uncurry : (E⟿F⟿G)⟿(E×F⟿G) := detail.uncurry'

    lemma unwrap (f : E⟿F) (x : E) : f x = f.1 x := begin unfold coe_fn, unfold has_coe_to_fun.coe, end

    @[simp] lemma id_apply (x : E) : id x = x := begin unfold id, repeat {rw unwrap}, simp, end
    @[simp] lemma comp_apply (f : F⟿G) (g : E⟿F) : comp f g = f.comp g := begin ext, simp, unfold comp, repeat {rw unwrap}, end
    @[simp] lemma curry_apply (f : E×F⟿G) (x : E) (y : F) : curry f x y = f (x,y) := begin unfold curry, repeat {rw unwrap}, end
    @[simp] lemma uncurry_apply (f : E⟿F⟿G) (p : E×F) : uncurry f p = f p.1 p.2 := begin unfold uncurry, repeat {rw unwrap}, end
    @[simp] lemma uncurry_curry : ((uncurry.comp curry) : (E×F⟿G)⟿(E×F⟿G)) = id := begin ext, simp, end
    @[simp] lemma curry_uncurry : ((curry.comp uncurry) : (E⟿F⟿G)⟿(E⟿F⟿G)) = id := begin ext, simp, end

  end smooth

end convenient


