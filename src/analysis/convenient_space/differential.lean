import analysis.convenient_space.smooth_map
import analysis.convenient_space.smooth_linear_map
import analysis.convenient_space.exponential

reserve prefix `δ`: 1500

namespace convenient

  section differential
    variables 
      {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
      {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
      {G : Type*} [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G] 

    namespace detail
      /- This namespace containes some helper functions to define final differential. -/

      @[reducible] noncomputable def diff.core (f : E⟿F) (x dx : E) : F := 
        smooth_curve.deriv ⟨f ∘ (smooth_curve.line x dx), begin apply f.2, tauto, end⟩ 0

      noncomputable def diff.to_fun : (((E⟿F)×E)×E)→F := 
        λ fxdx, 
          let f := fxdx.1.1 in
          let x := fxdx.1.2 in
          let dx := fxdx.2 in 
          diff.core f x dx

      lemma diff.is_smooth : is_smooth (diff.to_fun : (((E⟿F)×E)×E)→F) := sorry
      noncomputable def diff : (((E⟿F)×E)×E)⟿F := ⟨diff.to_fun, diff.is_smooth⟩

    end detail

    /- TODO: Here I might need that E and F are convenient vector spaces, but I'm not sure. -/
    /- The differential could be also defined as `diff : (E⟿F)⊸(E⟿(E⊸F))`. -/
    /- However, mixing smooth and linear maps would get us into a coercion hell, or at least I do not know how to avoid it -/
    noncomputable def diff : (E⟿F)⟿(E⟿(E⟿F)) := (detail.diff).curry.curry
  
    notation δ f := diff f


    /- Let's prove basic properties, but keep them inside of smooth_map namespace -/
    /- Similar statements will be stated in the `smooth` namespace in generality -/
    namespace smooth_map

      variables {f : F⟿G} {g : E⟿F} {x dx dx': E} {s : ℝ}
  
      noncomputable def line (x dx : E) : ℝ⟿E := ⟨λ t, x + t • dx, sorry⟩
      lemma line.diff {t dt : ℝ} : δ (line x dx) t dt = dt • dx := sorry
  
      /- This is the crux of the chain rule! -/
      lemma diff.curve_independence (c₁ c₂ : ℝ⟿E) : δ c₁ 0 1 = δ c₂ 0 1 → δ (g.comp c₁) 0 1 = δ (g.comp c₂) 0 1 := sorry
  
      lemma diff.by_line : δ g x dx = δ (g.comp (line x dx)) 0 1 := sorry
  
      @[simp] lemma comp.diff : δ (f.comp g) x dx = δ f (g x) (δ g x dx) := 
      begin 
        transitivity δ (f.comp (line (g x) (δ g x dx))) 0 1,
        { rw diff.by_line, 
          rw smooth_map.comp.assocr,
          apply diff.curve_independence,
          rw ← diff.by_line,
          rw line.diff, simp, },
        { rw ← diff.by_line }
      end
  
    end smooth_map

    variables {f : F⟿G} {g : E⟿F} {x dx dx': E} {s : ℝ}
    @[simp] lemma diff.smul_apply : δ g x (s•dx) = s • (δ g x dx) := sorry
    @[simp] lemma diff.add_apply : δ g x (dx+dx') = δ g x dx + δ g x dx' := sorry
    @[simp] lemma diff.zero_apply : δ g x 0 = 0 := sorry

    end differential

end convenient
