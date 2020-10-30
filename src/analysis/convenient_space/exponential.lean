import analysis.convenient_space.smooth_map

namespace convenient

  /- State Cartesian Closedness -/
  section cartesion_closedness
    variables 
      {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
      {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
      {G : Type*} [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G] 

    /- This is a bit convoluted, but you need to prove this to cast `f` to E⟿F⟿G -/
    /- The problem is that to even state smoothness in x, you need a proof of smoothness in y for all x -/
    def is_smooth_in_two_args (f : E→F→G) : Prop := 
      ∃ (h : (∀ (x : E), is_smooth (f x))),  /- smooth in y -/
        is_smooth (λ (x : E), (⟨f x, h x⟩ : F⟿G)) /- smooth in x -/

    noncomputable def mk_smooth2 (f : E→F→G) (h : is_smooth_in_two_args f) : E⟿F⟿G := 
      ⟨λ x, ⟨λ y, f x y, begin induction h, apply h_w end⟩, begin induction h, apply h_h, end⟩

    lemma smooth_in_two_args (f : E⟿F⟿G) : is_smooth_in_two_args (λ x y, f x y) := 
      begin split, simp, apply f.2, intro, simp, apply (f x).2, end

    --   ___          _          _              ___ _                _
    --  / __|__ _ _ _| |_ ___ __(_)__ _ _ _    / __| |___ ___ ___ __| |_ _  ___ ______
    -- | (__/ _` | '_|  _/ -_|_-< / _` | ' \  | (__| / _ (_-</ -_) _` | ' \/ -_|_-<_-<
    --  \___\__,_|_|  \__\___/__/_\__,_|_||_|  \___|_\___/__/\___\__,_|_||_\___/__/__/
    /- TODO: the main theorem to prove -/
    theorem cartesian_closedness (f : E×F→G) : 
       is_smooth f ↔ is_smooth_in_two_args (λ x y, f (x,y)) := sorry

  end cartesion_closedness

  namespace smooth_map
    variables 
      {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
      {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
      {G : Type*} [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G] 
    
    /- smooth_map.curry and smooth_map.uncurry are here just to bootstrap smooth.curry and smooth.uncurry -/
    /- Thus as a user, prefer using smooth.curry and smooth.uncurry -/
    noncomputable def curry (f : E×F⟿G) : (E⟿F⟿G) := 
      mk_smooth2 (λ x y, f (x,y)) ((cartesian_closedness f).1 f.2)
    noncomputable def uncurry (f : E⟿F⟿G) : (E×F⟿G) := 
      ⟨λ p, f p.1 p.2, begin apply (cartesian_closedness _).2, apply smooth_in_two_args, end⟩

    @[simp] lemma curry_apply (f : E×F⟿G) (x : E) (y : F) : f.curry x y = f (x,y) := 
      begin unfold curry, unfold mk_smooth2, repeat {rw unwrap},  end
    @[simp] lemma uncurry_apply (f : E⟿F⟿G) (p : E×F) : f.uncurry p = f p.1 p.2 := 
      begin unfold uncurry, repeat {rw unwrap}, end
    @[simp] lemma uncurry_curry (f : E×F⟿G) : f.curry.uncurry = f := 
      begin ext, simp, end
    @[simp] lemma curry_uncurry (f : E⟿F⟿G) : f.uncurry.curry = f := 
      begin ext, simp, end

  end smooth_map

end convenient
