import analysis.convenient_space.smooth_map

namespace convenient

  class convenient_space (E : Type*) 
    [add_comm_group E] [vector_space ℝ E] 
    [τ : topological_space E] [locally_convex_space ℝ E] : Prop :=
    (cinf_complete : 
      ∀ (f : curve E),
        (∀ (μ : E →L[ℝ] ℝ), curve.is_smooth (μ∘f) ) → f.is_smooth)
  
  

end convenient
