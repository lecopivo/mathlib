import analysis.convenient_space.smooth_map
import analysis.convenient_space.smooth_linear_map

namespace convenient
  section differential
    variables 
      {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
      {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 


    noncomputable def diff : (E⟿F)⊸(E⟿(E⊸F)) := 
      ⟨λ f, ⟨λ x, ⟨λ dx, smooth_curve.deriv ⟨f ∘ (smooth_curve.line x dx), begin apply f.2, tauto, end⟩ 0,
          /- smoothness in dx -/ sorry, sorry⟩, 
          /- smoothness in x -/ sorry⟩, 
          /- smoothness in f -/ sorry, sorry⟩


    end differential



end convenient
