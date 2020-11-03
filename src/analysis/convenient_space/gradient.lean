import analysis.normed_space.inner_product
import analysis.convenient_space.compile_smooth
import analysis.convenient_space.differential
import analysis.convenient_space.has_smooth_version

reserve prefix `∇`: 1500

noncomputable theory

namespace convenient

  variables {E F : Type*} 
    [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
    [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F]

  variables (E)

  class self_dual :=
    ( to_dual : E⊸(E⊸ℝ) ) -- E⊸(E⊸ℝ) once linear maps have full support
    ( from_dual : (E⊸ℝ)⊸E ) -- (E⊸ℝ)⊸E once linear maps have full support
    ( from_to_dual : from_dual ∘ to_dual = id )
    ( to_from_dual : to_dual ∘ from_dual = id )


  variables {E}

  @[reducible] def to_dual [self_dual E] : E⊸(E⊸ℝ) := self_dual.to_dual
  @[reducible] def from_dual [self_dual E] : (E⊸ℝ)⊸E := self_dual.from_dual

  instance prod.self_dual [self_dual E] [self_dual F] : self_dual (E×F) := 
    { to_dual := sorry, -- I need linear combinators - (linear.comp linear.add).comp $ linear.pair_map.comp $ (self_dual.to_dual : E⊸(E⊸ℝ)).pair_map (self_dual.to_dual : F⊸(F⊸ℝ))
      from_dual := sorry, -- I need linear combinators - (linear.comp linear.add).comp $ linear.pair_map.comp $ (self_dual.to_dual : E⊸(E⊸ℝ)).pair_map (self_dual.to_dual : F⊸(F⊸ℝ))
      to_from_dual := sorry,
      from_to_dual := sorry,
    }
    
  variables [self_dual E]

  @[simp] lemma from_to_dual (x : E) : from_dual (to_dual x) = x := begin transitivity (from_dual ∘ to_dual) x, simp, rw self_dual.from_to_dual, simp, end

  @[simp] lemma to_from_dual (x : E⊸ℝ) : to_dual (from_dual x) = x := begin transitivity (to_dual ∘ from_dual) x, simp, rw self_dual.to_from_dual, simp, end


  section gradient
    variables 
      [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E] [self_dual E]
      [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] [self_dual F]
    
    /-- Potentially:  def grad : (E⟿F)⟿(E⟿E⊗F) -- I'm not sure if this is entirely possible --/
    def grad : (E⟿ℝ)⟿(E⟿E) := by compile_smooth ```(λ (f : E⟿ℝ) (x : E), from_dual (Diff f x))

    notation ∇ f := grad f

    @[simp] def grad.apply (f : E⟿ℝ) (x v : E) : to_dual (∇ f x) v = δ f x v := begin unfold grad, simp, end

  end gradient

end convenient
