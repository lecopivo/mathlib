import analysis.convenient_space.smooth_map
import analysis.convenient_space.smooth_linear_map

reserve prefix `δ`: 1500

namespace convenient
  section differential
    variables 
      {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
      {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
      {G : Type*} [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G] 

    namespace detail
      /- This namespace containes some helper functions to define final differential. -/

      @[reducible] noncomputable def diff_core (f : E⟿F) (x dx : E) : F := 
        smooth_curve.deriv ⟨f ∘ (smooth_curve.line x dx), begin apply f.2, tauto, end⟩ 0
  
      lemma diff'''.is_linear (f : E⟿F) (x : E) : is_linear_map ℝ (diff_core f x) := sorry
      lemma diff'''.is_smooth (f : E⟿F) (x : E) : is_smooth (diff_core f x) := sorry
      @[reducible] noncomputable def diff''' (f : E⟿F) (x : E) : E⊸F := ⟨⟨λ dx, diff_core f x dx, diff'''.is_smooth f x⟩, diff'''.is_linear f x⟩
  
      lemma diff''.is_smooth (f : E⟿F) : is_smooth (diff''' f) := sorry
      @[reducible] noncomputable def diff'' (f : E⟿F) : E⟿(E⊸F) := ⟨λ x, diff''' f x, diff''.is_smooth f⟩
  
      lemma diff'.is_linear : is_linear_map ℝ (diff'' : (E⟿F)→(E⟿(E⊸F))) := sorry
      lemma diff'.is_smooth : is_smooth (diff'' : (E⟿F)→(E⟿(E⊸F))) := sorry
      @[reducible] noncomputable def diff' : (E⟿F)⊸(E⟿(E⊸F)) := ⟨⟨λ f, diff'' f, diff'.is_smooth⟩, diff'.is_linear⟩

    end detail

    /- TODO: Here I might need that E and F are convenient vector spaces, but I'm not sure. -/
    noncomputable def diff : (E⟿F)⊸(E⟿(E⊸F)) := detail.diff'
  
    notation δ f := diff f

    variables {f : F⟿G} {g : E⟿F}

    lemma comp.diff (x dx : E) : δ (f.comp g) x dx = δ f (g x) (δ g x dx) := sorry

    end differential

end convenient
