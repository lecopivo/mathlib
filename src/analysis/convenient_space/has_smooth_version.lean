import analysis.convenient_space.smooth

noncomputable theory

namespace convenient
  variables 
    {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
    {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
    {G : Type*} [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G] 
    {H : Type*} [add_comm_group H] [vector_space ℝ H] [topological_space H] [locally_convex_space ℝ H] 

  instance prod.mk.arg2.has_smooth_version (x : E) : has_smooth_version (prod.mk x : F→E×F) :=
    { func := smooth.pair x,
      eq := rfl }

  instance neg.has_smooth_version (x : E) : has_smooth_version (has_neg.neg : E→E) :=
    { func := smooth.neg,
      eq := rfl }

  instance add.arg2.has_smooth_version (x : E) : has_smooth_version (has_add.add x : E→E) :=
    { func := smooth.add x,
      eq := rfl }

end convenient
