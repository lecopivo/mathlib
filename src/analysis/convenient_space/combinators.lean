import analysis.convenient_space.smooth_map
import analysis.convenient_space.smooth

noncomputable theory

namespace convenient

  namespace combinators.smooth

    variables {E F G : Type*} 
    variables [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
    variables [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F]
    variables [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G]

    open smooth

    def I : E⟿E := id
    def K : E⟿F⟿E := const
    def B : (F⟿G)⟿(E⟿F)⟿(E⟿G) := comp
    def C : (E⟿F⟿G)⟿(F⟿E⟿G) := swap
    def S :=  
      (eval.comp $
       (eval.pair_map eval).comp $
       perm.ac_bd.comp $ 
       ((id : (E⟿F⟿G)×(E⟿F)⟿(E⟿F⟿G)×(E⟿F) ).pair_map diag)).curry.curry

    @[simp] lemma I_apply (x : E) : I x = x := begin unfold I, simp, end
    @[simp] lemma K_apply (x : E) (y : F) : K x y = x := begin unfold K, simp, end
    @[simp] lemma B_apply (f : F⟿G) (g : E⟿F) (x : E) : B f g x = f (g x) := begin unfold B, simp, end
    @[simp] lemma C_apply (f : E⟿F⟿G) (x : E) (y : F) : C f y x = f x y := begin unfold C, simp, end
    @[simp] lemma S_apply (f : E⟿F⟿G) (g : E⟿F) (x : E) : S f g x = (f x) (g x) := begin unfold S, simp, end

  end combinators.smooth


end convenient
 
